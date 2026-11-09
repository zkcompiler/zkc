# Exact finite table predicates

`PIR.Relation.Table` in
[`TableRelation.lean`](../../program/Zkc/Program/Semantics/TableRelation.lean) is an independent
model over any type with decidable equality. Tables are lists, queries retain a
Boolean active flag, and coordinates are natural numbers.

`contains_exact` proves the left-fold membership scan returns true exactly when
the value occurs. `membership_exact` proves the masked left fold returns true
exactly when every active query value occurs. `indexedRead_exact` relates a
coordinate scan to `table[position]? = some value`; absent coordinates are
false. Duplicate queries do not consume multiplicity, and active/inactive
queries on an empty table have different outcomes.

These are complete Boolean decision laws on the model. The previous generated
membership/indexed-read subjects, source-view equations and clause installations
are retired. Native table execution remains supported and tested separately;
these mathematical laws do not certify its representation or an AIR/lookup
security reduction.

The [native contract](../../../docs/spec/ir/execution.md) and
[table library](../../../libraries/relations/table/README.md) own the executable
behavior. A new source connection must associate the actual helper bodies,
eager evaluation, finite-domain admission, output order and stopped outcomes
before applying these mathematical laws.
