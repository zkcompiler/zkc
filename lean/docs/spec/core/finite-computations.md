# Ordered finite computations

This chapter specifies the independent `Zkc.FiniteComputation` model in
[`Zkc/Semantics/FiniteComputation`](../../../Zkc/Semantics/FiniteComputation).
It defines values and first failures after eager operand evaluation. It does
not interpret native source, MLIR, runtime instructions or resource accounting.
[The correspondence map](../../correspondence/finite-computations.md) records
proved laws and the obligations of a future implementation bridge.

## Enumeration and admission

An enumeration is a `List α`, not a set of values. Its positions determine
traversal order and multiplicity. `[2, 2, 3]` therefore has three occurrences,
including two contributions of `2`. There is no implicit sorting or deduplication.
The item type is independent of the computation's result algebra.

`Domain α` describes already evaluated immutable inputs with four constructors:

- `elements items` preserves exactly the supplied list.
- `guard check domain` first checks an `Except String Unit` admission result,
  then admits the child on success. A guard represents an admission requirement;
  it is not a thunk for evaluating source operands or captures.
- `zip left right` admits the left child, then the right child, and then requires
  their lengths to agree. A mismatch returns `finite-zip-shape`. Only after all
  this succeeds does it expose the pair list. Nested binary zip supports any
  fixed number of heterogeneous inputs; every child participates even if the
  body ignores its value or another child is empty.
- `product left right` admits both independent children in written order, then
  enumerates pairs with the left coordinate outermost. An empty child does not
  suppress admission of the other child. No equal-length premise is required.

`Domain.enumerate` stops at the first admission failure. “All checks” means all
checks are required for success, not that checks continue after a failure.
Structural nesting fixes admission order. This chapter does not assert a
flattened global priority between every provider check and every zip check.
A future bridge must match the concrete chosen order to this description or
supply a refined admission model.

The list of product pairs specifies order; its use in this reference does not
require a native implementation to allocate that list. Conversely, a successful
unbounded Lean enumeration says nothing about native memory or work limits.

## Total computation

`Total.collect items keep body` is `(items.filter keep).map body`, preserving the
order of selected occurrences. `keep : α → Bool` and `body : α → β` are total
functions. False predicates exclude body evaluation from the selected meaning.

`Total.fold items keep body step initial` left-folds those selected results.
`step : σ → β → σ` is arbitrary and total: the item `α`, body result `β` and
accumulator `σ` can all differ. An empty fold returns `initial`. Associativity,
commutativity and a monoidal identity are not requirements of an ordered fold.

`productMap` and `sumMap` specialize total collection to Mathlib's ordered list
product and sum. Monoid or additive monoid laws permit adjacent chunking and
homomorphism transport. Permuting occurrences additionally requires a
commutative monoid or additive commutative monoid; multiplicities still remain.
These class instances are mathematical hypotheses, not laws inferred from an
executable callback or a notation spelling.

## Local computation

The Local boundary uses the existing `Except String` type. An outcome is a
successful value or the first error string. No persistent store, trace,
protocol effect, allocator, budget or residual accumulator is observed on a
failure. In particular, this type is not the complete `PIR.Execution` model.

`Local.select keep body item` evaluates the predicate first. On false it returns
`none` without invoking the body. On true it invokes the body and returns
`some value`. Predicate and body errors propagate without being replaced.

`Local.collect` uses `List.filterMapM` to materialize selected body results in
order. `Local.fold` uses `List.foldlM`: for each item it selects, computes the
body if selected, and immediately updates the explicit accumulator. A
predicate, body or update error prevents entry into the remaining suffix.
Local callbacks are total Lean functions returning explicit success or error;
this does not model divergence of arbitrary native code.

`Local.runFold` admits a `Domain` before entering any callback. Empty or entirely
filtered computations still require admission. The domain operands, initial
state and callback environments are inputs already evaluated at this boundary;
the definition cannot establish their source evaluation order.

`Local.nestedFold outer inner step initial` enters `inner item` on each reached
outer occurrence, then left-folds its returned items. The inner computation may
depend on that outer item and may fail. An empty outer list never enters it.
An earlier update failure also prevents later inner entry. This differs from
independent product admission. Each lexical inner entry must include its own
operand evaluation, captures and checks in any future bridge.

## Materialization and streaming

`Local.materialize items keep body reducer` first completes `Local.collect`,
then invokes `reducer : List β → Except String ρ` once, including when the
collected list is empty. The reducer may inspect length or every element, fail,
and return a type different from both the item and the body result.

There is no general equation between an ordinary reducer and a streaming fold.
Even when the reducer is itself a left fold, moving an update across a later
body can change the first failure: a second-body failure is observed before a
first-update failure under materialization; streaming observes the first update
failure instead. The maintained tests decide this counterexample.

Two sufficient conditions are proved for replacing a materialized left fold:

1. If the update is a total function `σ → β → σ`, materialization and streaming
   have the same `Except` outcome even when predicates or bodies fail.
2. If the predicate and body are total, they may be materialized before an
   update `σ → β → Except String σ` that can fail.

Both conditions rely on the absence of separately observable effects in this
model. They establish neither identical traces nor identical allocations or
resource exhaustion. Neither makes an arbitrary reducer an incremental fold.

## Mathematical consumers

The [realization module](../../../Zkc/Semantics/FiniteComputation/Realization.lean)
connects admitted equal-length multiplication/sum to the existing independent
`FiniteVectors.dot`, under that model's extent bound. Its failure codes and
admission surface are not equated to arbitrary domain admission.

Heterogeneous point/scalar zip yields a weighted sum under `Semiring R`,
`AddCommMonoid M` and `Module R M`. Scalar scaling retains multiplication order.
Enumerating `Fin n` positions connects ordered sums to the existing
`Zkc.Algebra.linearCombination`; matrix contraction reuses its row law with
explicit finite row and column axes. These are module-valued mathematical
results, not a proof of a concrete curve MSM, matrix codec or native kernel.
