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
witness existence. The retained `TableMembershipData` and `TableIndexedReadData`
subjects come from the actual table library protocols. Their `Views` modules
admit the complete original units, including nominal queries, both finite-fold
callbacks, checked-read premises and the original Local realizations. Exact
body associations connect each equation to those admitted helper definitions.

[`TableMembershipLaws`](../../ZkcExamples/Structured/TableMembershipLaws.lean)
proves the actual membership formula returns the complete Boolean decision on
exactly this source-model domain:

```text
queries.length < 2^64 ∧ (queries = [] ∨ table.length < 2^64)
```

Outside this domain the formula stops exhausted. The source's Boolean operations
are eager: an inactive query still invokes the inner table scan. Empty queries
invoke no callback and require no table-length premise. Ordered query fields,
including inactive values, remain in the nominal source and statement carriers.

[`TableIndexedReadLaws`](../../ZkcExamples/Structured/TableIndexedReadLaws.lean)
proves the indexed-read formula returns its complete decision when the table
length is below `2^64`, and stops exhausted otherwise. Every reached read is in
range because the loop enumerates table indices. The requested natural position
can be arbitrary; an absent coordinate returns false. A native index port has
its separate representation admission.

[`TableContractBindings`](../../ZkcExamples/Structured/TableContractBindings.lean)
selects the actual `selected_rows` and `selected_read` clauses, their ordered
applications and retained formula symbols. It discharges both `FormulaLaw`
obligations under these domains against the mathematical predicates above.
This connection uses the existing relation interpretation and helper table.
General finite-computation admission supplies structural closure; the narrower
immediate-return profile supplies its own distinct return evidence.

The formula equations use the structured model's uniform scalar carrier with
decidable equality. They establish neither native KoalaBear representation and
execution correspondence nor an AIR/lookup security reduction. The bridge's
bounded replay controls exercise only equality of canonical KoalaBear values;
current native table execution is tested separately.

The Exec outcome contract uses the existing `PIR.Outcome`, `PIR.Execution` and
`Execution.follow` model. In particular a stopped outcome preserves its actual
state and event prefix and never invokes a continuation. No second execution
monad or new formal carrier is introduced for the native Data/Exec operation
layout. The [native contract](../../../docs/spec/ir/execution.md) and
[table library](../../../libraries/relations/table/README.md) record their own
implementation evidence.
