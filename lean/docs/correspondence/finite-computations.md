# Finite computation correspondence

This map covers the [independent finite computation specification](../spec/core/finite-computations.md).
All declarations below are in `Zkc.FiniteComputation`. A theorem relates these
Lean definitions under the listed premises; it does not assert correspondence
to the current native compiler. The [support page](../support.md#ordered-finite-computations)
records the maintained capability boundary.

## Definition and theorem map

| Clause | Declarations | Exact premise or limit |
|---|---|---|
| Ordered enumeration, duplicates | `Domain.elements`, `Domain.enumerate`, `Total.collect` | Supplied lists retain occurrences; no set conversion |
| Heterogeneous strict zip | `Domain.zip_ok`, `zip_mismatch`, `zip_elements` | Success is equivalent to both successful children, equal extents and their exact zipped list; recursively retains all children |
| Independent product | `Domain.product_ok`, `product_empty_right_error` | Lexicographic list, both child admissions required, even for empty products |
| Stable filtering | `Local.select_false`, `select_error` | False skips the body; predicate error wins over body behavior |
| Ordered total fold | `Total.fold_append` | Arbitrary total step, adjacent chunks retain order and intermediate state |
| Ordered Local fold | `Local.fold_append`, `fold_prefix_error` | Exact `Except` equality, including first failure; no residual state on error |
| Domain entry | `Local.runFold_error` | Any admission error propagates independently of all callbacks and initial value |
| Dependent entry | `Local.nestedFold_nil`, `nestedFold_total_inner` | Empty outer skips inner; flattening theorem requires total inner enumeration and keeps outer-then-inner order, with arbitrary failing updates |
| Total/Local boundary | `Local.collect_total`, `fold_total`, `runFold_total` | Explicit total callbacks; `runFold_total` additionally requires successful domain enumeration |
| Materialized reducer | `Local.materialize_error` | Collection error prevents reducer invocation, for any reducer/result type |
| Streaming equivalence | `Local.materialize_total_step` | Update total; predicate and body may fail; exact first error preserved |
| Alternative streaming condition | `Local.fold_total_selection`, `materialize_total_selection` | Predicate and body total; update may fail |
| Monoidal realization | `productMap_fold`, `sumMap_fold` | Monoid/additive monoid, arbitrary initial state; no commutativity |
| Adjacent grouping and map fusion | `productMap_append`, `productMap_map`, `productMap_flatMap`, and their `sumMap` counterparts | Total bodies, list order and multiplicity retained; dependent pure inner lists allowed |
| Algebraic transport | `productMap_hom`, `sumMap_hom` | Explicit monoid/additive homomorphism |
| Reordering | `productMap_perm`, `sumMap_perm` | Commutativity and `List.Perm`, preserving duplicates |
| Failure-aware additive reduction | `materialize_sum` | Total addition under `AddMonoid`; predicate/body errors retained |
| Independent dot consumer | `dot_admitted` | Equal lengths, existing vector bound, commutative ring; no arbitrary extra operands removed |
| Heterogeneous weighted sum | `msm_admitted`, `weighted_sum_scale` | Equal point/scalar lengths for admission; semiring acting on additive commutative monoid; scalar multiplication order retained |
| Indexed and matrix contractions | `sumMap_linearCombination`, `matrix_contraction` | Explicit `Fin` axes, module laws and commutative addition; reuses `Zkc.Algebra.linearCombination_rows` |

## Compatibility with existing independent models

This model uses Lean's existing list traversal and `Except String` machinery,
Mathlib's monoids and module laws, and the existing finite-vector dot and module
contraction definitions. It introduces no source expression grammar or native
representation. The generic domain is not a replacement for bounded vector or
matrix admission: bounds can be represented as guards, but are not imposed on
all abstract domains.

Existing ring-expression pointwise maps admit every original operand, including
unused rows. Their checks cannot be reduced to those of the two selected dot
inputs using `dot_admitted`. An adapter must first retain the full original
admission, then relate the admitted row evaluation to this enumeration. An
ordinary vector-to-scalar reduction is represented by `Local.materialize`; it
requires an additional proved reducer law before using a streaming theorem.

## Future native bridge obligations

A bridge must identify a concrete source/IR version, its interpreter and a value
relation, then discharge the following obligations. These are open obligations,
not assumptions silently supplied by the current theorems.

| Boundary | Required evidence |
|---|---|
| Formation and fixed mode | Relate each checked item, result and accumulator type and the selected Math/Local callable. Check every intermediate, including unused operations and empty-domain bodies. Lack of protocol effects alone does not prove totality. |
| Static scoped bodies | Preserve resolved binder identities, shadowing, static helper/component bindings, specialization and argument order. A callback value in Lean does not verify the native nonescaping scoped-argument discipline. |
| Eager entry | Relate written evaluation order of domain source operands, explicit initial state and capture snapshots, including any earlier failure. Only then relate composite admission. Initial/capture failure may precede even a known shape mismatch. |
| Captures and ownership | Relate actual immutable values and exact free places, including projection overlap, evaluation order and read-once snapshots. Prove Copy/Drop and affine-state obligations, role availability and absence of implicit protocol actions. |
| Domain interpretation | Prove exact storage/range/view order, duplicate occurrences, extent arithmetic, checked bounds and matrix axes. For zip, retain every child's admission even when unused or empty. Match left-to-right first failure and the concrete placement of composite checks. |
| Independent versus nested entry | Prove independent operands are evaluated once at entry. Prove inner operand/capture/check computations run only at each reached outer occurrence; no hoisting across emptiness or prior failure. |
| Total access | Connect index provenance to the exact immutable container and extent; a `Fin` bound or coincidentally equal length alone does not prove container identity. Validate half-open/reversed ranges and machine arithmetic before using a total enumeration. |
| Callback execution | Relate successful body/update values and exact stopping behavior at each reached invocation. Establish predicate-before-body order and skipped bodies; relate local mutation and state to the explicit accumulator. |
| Complete executions | Explain how native stop codes and residual state map to `Except String`. Prove separately any observable store, trace, cleanup or persistent consumed-resource property: failed accumulators and such effects are absent here. |
| Reducer interpretation | Prove an ordinary reducer equals the chosen materialized operation for every admitted input, including empty input and length-sensitive/failing reducers. Prove one of the streaming theorem conditions or a stronger effect-aware commutation theorem before interleaving updates. |
| Algebra and representation | Supply actual field/group/module meanings and homomorphisms for codecs, scalar action and installed arithmetic. Match all operand admission, row/column orientation and occurrence multiplicity for dot/MSM/matrix candidates. Algebraic shape recognition alone supplies none of these laws. |
| Resources and implementation | Prove or measure the declared relation between scalar loops and bulk kernels for entered work, checked arithmetic, materialization, allocation and exhaustion. Do not infer preservation of the same resource cap from a value/error theorem without resources. Relate lowering, independent artifact validation and actual runtime execution. |

Any statement of native correspondence must name the obligations discharged and
its remaining restrictions. No theorem here validates the native notation,
source witness, dependency analysis, optimization recognizer or backend.

## Controls and reproduction

[`Tests.FiniteComputation`](../../Tests/FiniteComputation.lean) contains
kernel-checked positive instances and counterexamples plus an executable
`Tests.Checks` suite. Controls cover duplicate values, strict heterogeneous and
multiway zip, ignored and empty extents, first admission failure, independent
versus dependent entry, filtered failures, materialized/streaming failure order,
empty reducer invocation, distinct item/result/state types, nonassociative and
noncommutative folds, and dot/MSM/matrix consumers.

[`Tests.FiniteComputationAudit`](../../Tests/FiniteComputationAudit.lean) imports
both the library and controls before auditing them, including private and
generated declarations. It uses the existing allowed-axiom policy and does not
weaken it. The ordinary Lake library/test globs include all these modules; the
aggregate audit imports are maintained by the existing generator.

From `lean/`, using the pinned dependencies:

```sh
lake build Tests.FiniteComputationAudit
lake env lean Tests/FiniteComputation.lean
lake env lean Tests/FiniteComputationAudit.lean
python3 checks/audit_imports.py --main-only
python3 checks/check_library.py --main-only --lake lake
```

The focused audit and executable controls are not a fresh whole-package build,
an optional-integration check, or native compiler/runtime validation.
