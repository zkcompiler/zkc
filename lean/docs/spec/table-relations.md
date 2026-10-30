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

## Actual plain construction consumer

`ZkcExamples.Construction.TableMembership` imports the unchanged library target
and checks the actual native plain producer/validator pair. The policy has no
selected service, suite or draw pair; the real validator ABI is a vector and a
sequence of the nominal Query product, with its sole Boolean output retained.
The source input tuple determines both prepared participant frames.

`validator_binding` is one complete all-environment Process equation.
`helper_equation`, `validator_equation`, `validate_equation` and `pair_equation`
reuse the actual helper closure and preserve every checkpoint, oracle/proof
state and exhausted scan. `target_agreement` connects the retained formula to
mathematical selected membership under the explicit reached bounds above.
`membership_completeness` proves success of the admitted actual pair under
those bounds; `membership_false_rejected` proves rejection of mathematical
false statements under every reply, including executions that exhaust bounds.
There are related inputs with both empty queries and a nonempty selected row.
No empty-schedule premise is used as a soundness proof. Inactive query values remain in the bound input data.
These are nominal constructed-model theorems, without a selected codec/native
execution realization or a new baseline acceptance.

`ZkcSecurityExamples.TableMembership.Subject` fixes that same admitted pair,
`selected_rows` clause and catalogue-compatible prime field `ZMod 2130706433`.
The shared `Generation.SubjectABI` emits the full source input tuple, exact
plain participant frames and a separate semantic initial public history. That
history binds both query fields, including inactive values; no transcript value
is appended to either participant frame. Optional inputs, representation bounds
and any retained input clauses keep the existing honest-input meaning.

`Method.compiled_ideal_complete` proves canonical perfect completeness with an
actual related admitted input and the actual producer execution.
`Method.bridge` and `Method.rejects` reuse the same whole-validator equation and
helper mathematics as completeness. They preserve exhausted inputs and prove
rejection independently of the empty charge schedule. Soundness quantifies
every raw typed statement and proof, without an honest-input bound.
`Method.adaptive_zero` also removes the adversary query-count premise, using
the existing zero-cost theorem for arbitrary terminating oracle computations.
`Claims` registers the existing canonical completeness and adaptive soundness
meanings and closes their required construction/source links at zero error;
it also supplies an empty charged receipt. The generic random-oracle interface
remains available to the adversary, while the actual plain validator makes no
query. These receipts cover the compiled ideal model, without a native runtime
or byte-codec correspondence claim. The [focused driver](../../security/checks/check_table_membership.py)
regenerates the ABI and endpoint and checks the receipts and refusal controls.
