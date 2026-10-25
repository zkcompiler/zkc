# Exact finite table predicates

`PIR.Relation.Table` in
[`TableRelation.lean`](../../Zkc/Semantics/TableRelation.lean) is an independent
model over any type with decidable equality. Tables are lists, queries retain a
Boolean active flag, and coordinates are natural numbers.

`contains_exact` proves the left-fold membership scan returns true exactly when
the value occurs. `membership_exact` proves the masked left fold returns true
exactly when every active query value occurs. `indexedRead_exact` relates a
coordinate scan to `table[position]? = some value`; absent coordinates are
false. Duplicate queries do not consume multiplicity, and active/inactive
queries on an empty table have different outcomes.

These are complete Boolean decision laws on the model, not merely positive
witness existence. They justify interpreting the corresponding mathematical
predicates when a selected source-formula connection supplies its own
`FormulaLaw`. They do not provide that source-body connection, a native
representation or execution bridge, or a security reduction for an AIR/lookup
argument. Existing structured-source relation/application bindings retain
actual formula references, roles and selectors; importing those records does
not prove evaluator adequacy automatically.

The current structured-source export profile accepts ordered sequences of
nominal products, including the represented `Query<F>` shape. It refuses a
Local realization containing a finite fold, including the indexed scan, with
`structured-source-realization` because finite folds are outside that
realization profile. The native examples therefore do not yet have a
structured-source import into this model. Completing that boundary requires
finite computation admission distinct from unconditional immediate return,
followed by an actual source-formula law with explicit domain bounds. This restriction
does not change the mathematical predicate or the native evaluator's support.

The Exec outcome contract uses the existing `PIR.Outcome`, `PIR.Execution` and
`Execution.follow` model. In particular a stopped outcome preserves its actual
state and event prefix and never invokes a continuation. No second execution
monad or new formal carrier is introduced for the native Data/Exec operation
layout. The [native contract](../../../docs/spec/ir/execution.md) and
[table library](../../../libraries/relations/table/README.md) record their own
implementation evidence.
