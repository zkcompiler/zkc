# Adding one checked transformation

This example combines immutable preparation, stateful calls and query-plan
selection. Its source, successful execution and counterexamples are defined in
[Tests.PreparationComposition](../../formal/Tests/PreparationComposition.lean). It runs over
natural numbers in the Lean model; the final section explains the native handoff.

## 1. The source and proposed optimization

The source queries this polynomial at installed values of `x` and `y`:

```text
f(x,y) = 1 + 2x + (3 + 4x)y
```

Preparing at `x = 2` produces the coefficient table `[5,11]`, so a subsequent
query at `y = 3` can evaluate `5 + 11·3 = 38`. The direct plan evaluates the
original polynomial. A reuse plan reads the prepared table and substitutes the
remaining coordinate. The compiler must establish that these values agree in
the world where the query actually runs.

The [preparation input](../../formal/Zkc/Polynomial/Bilinear/Execution.lean) carries the
polynomial origin, four coefficients and the chosen `x`. These determine the
immutable preparation key. Changing `x` to `4` changes the key and produces
`[9,19]`. Changing only `y` does not change this table. Installing it in a second
namespace also preserves the key while giving its live references a separate
scope. These are properties of this preparation computation, not a rule that
every cache key may omit namespaces or remaining inputs. See [binding](artifact-binding.md).

## 2. Why writes and failed calls matter

The first four queries in the actual source encounter these transitions:

| Before the query | Safe plan | Result | Incorrect stale reuse |
|---|---|---|---|
| Install the table for `x = 2`, with `y = 3` | Reuse `[5,11]` | 38 | 38 |
| An external call writes `x = 4` and returns `false` | Direct evaluation | 66 | 38 |
| Install the table for `x = 4` | Reuse `[9,19]` | 66 | 66 |
| Another call overwrites the installed table's view with the constant `999` | Direct evaluation | 66 | 999 |

Here `false` is a returned call result, and the source continues along its
failure branch. It is not a rollback. The actual write invalidates the old
query fact. The alias overwrite also invalidates that fact even though the
immutable cache itself can remain valid. Cache validity and validity of an
installed view are separate invariants.

The analysis uses each call's interpreted postcondition to discard facts that
its writes may invalidate. `ignored_failure_write_is_wrong` and
`ignored_alias_write_is_wrong` calculate the two wrong answers above.
The [contract and state guide](contracts.md) states the general framing
obligations.

## 3. How the proof is assembled

1. `source_legal` establishes the actual source's call and input-readiness
   premises from the empty initial world. This finite instance check is distinct
   from a general frontend admission algorithm.
2. `external_laws` proves that both external implementations satisfy their
   contracts, including writes on failure. Sound fact transfer therefore applies
   to the actual successor states.
3. `checked_value` in [Demand](../../formal/Zkc/Modules/Factor.lean) equates a
   checked query plan with direct evaluation under valid facts. The analysis
   supplies plans and maintains those premises at their points of use.
4. `compile_with_preparation` in [Mixed](../../formal/Zkc/Polynomial/Bilinear/Execution.lean)
   combines the caller analysis with a relation between direct and memoized
   preparation handlers. Valid caches may differ; their logical worlds agree.
5. `compile_with_guards` in [Readiness](../../formal/Zkc/Polynomial/Bilinear/Compilation.lean)
   keeps runtime guards installed for legal callers. The example's `source_correct`
   instantiates it to obtain a complete execution relation with the chosen event
   view. Its legality premise ensures that reached demands do not refuse.

For a caller that actually reaches an unavailable demand,
[`compile_until_refusal`](../../formal/Zkc/Polynomial/Bilinear/Compilation.lean) instead
requires valid initial facts/cache and the preconditions of module calls reached
before that refusal. It preserves the stopped outcome and earlier state/events
without requiring legality of the unexecuted suffix. This is a separate joined
law; it does not change which theorem the original example instantiates.

This chain connects unary invariants to a relational compiler result. The
[theory chapter](../theory.md#2-analysis-facts-need-both-unary-and-relational-meanings)
explains why neither part can replace the other.

## 4. Results and the comparison baseline

The full source additionally reinstalls a prior preparation, shares it with a
second namespace at `y = 5`, and attempts an installation with insufficient
capacity. Both executions return:

```text
[38, 66, 66, 66, 38, 38, 60, 38]
```

`actual_outputs_and_costs` also checks the model's preparation charges:

| Execution | Preparation work | Saved work | Cache overhead | Work + overhead |
|---|---:|---:|---:|---:|
| Direct preparation and direct queries | 16 | 0 | 0 | 16 |
| Memoized preparation and inferred query plans | 8 | 8 | 6 | 14 |

These are declared model units, not timing, proof size or a complete machine
cost. They show a saving under this price model. An equally capable handwritten
library chooses exactly the same plans and execution (`library_has_same_plans`
and `library_has_same_execution`). The compiler's contribution here is automatic,
justified selection across calls, with no performance advantage over that library.

Further controls show that a rejected installation performs no preparation or
cache insertion, and that a demand with unavailable inputs stops with `refused`.
The general laws retain their stated hypotheses; the finite calculations make
this particular source and its adverse cases concrete.

## 5. Carrying the result into an implementation

A native pass must bind the same source, ordered captures and call meanings;
implement the selected plans and failure behavior; and relate native values,
buffers and state to this execution. These are the [realization](realization.md)
obligations for the first [implementation milestone](../roadmap.md).

Measure the generated route against both an equally capable library and the
pinned upstream implementation, separating compilation/checking from execution
cost. A pass that changes challenge order or wire language needs the corresponding
[transformation contract](../compiler/README.md); the cache theorem alone does
not justify that change.
