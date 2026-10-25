# Exact explicit-table relations

`table_relation` defines masked scalar-field membership and indexed reads over
an explicit ordered table. The reusable [source](lib.zkc) includes mathematical
evaluators, formula relations and ordinary protocol consumers. Its
[manifest](zkc.toml) depends only on collection and traversal libraries.

| API | Meaning |
|---|---|
| `Query<F>` | A Boolean active flag and the corresponding scalar-field value |
| `contains(table,value)` | Some table row equals the value |
| `membership(table,queries)` | Every active query value occurs in the table |
| `indexed_read(table,position,value)` | The exact in-range coordinate contains the value |
| `selected_queries(values,active)` | Ordered reached length admission, then query construction |
| `check_membership`, `check_read` | Ordered, potentially stopping execution of the total evaluator |
| `Membership`, `IndexedRead` | Retained source predicates, without adding a runtime guard themselves |
| `CheckMembership`, `CheckRead` | Direct verifier-table consumers with selected acceptance clauses |

Membership permits duplicate queries and duplicate table rows. It does not
consume rows or compare multisets. Empty selections are true; an active query
against an empty table is false. Out-of-range indexed reads are false. Positions
use native natural indices, not field residues. Selection length mismatch stops
before traversal, including when one side is empty.

The table parameter in each application is the actual verifier-local input.
Masks remain part of the query statement. Formula closure and application
selectors survive source export and independent comparison. A direct scan costs
O(table length × query count); indexed read currently scans O(table length).
These functions introduce no lookup VM instruction or proof system.

The [example](../../../examples/projects/table/README.md) exercises current
native execution and contrasts exact membership with the existing AIR
reciprocal equation. The [formal model](../../../lean/Zkc/Semantics/TableRelation.lean)
proves exact finite evaluator laws. The [retained-source laws](../../../lean/docs/spec/table-relations.md)
connect the complete original formulas to those predicates, with explicit
length bounds and exhausted outcomes. These laws supply neither native execution
correspondence nor a cryptographic lookup reduction. The
[shared relation contract](../../../docs/spec/relations.md) states the separate
encoding and proof obligations.
