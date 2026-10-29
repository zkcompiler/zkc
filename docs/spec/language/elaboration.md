# Checked source elaboration

The frontend owns the input contract for an independent source-elaboration
checker. Lean owns that checker's semantics and soundness theorem. The contract
is the existing `zkc.source-correspondence/0` publication, not the private native
elaborator's classes or a replacement Lean interface format. Both concrete
frontends must supply this same boundary during migration.

## Inputs and result

The exact [written-source contract](source-ast.md) defines the envelope and field
sets: `admission`, `source_ast`, `bindings`, `snapshot`, `instances`,
`instance_rows` and `rows`. Version zero has exactly one schema. Consumers reject
unknown/duplicate fields, duplicate identities, out-of-range paths, unsupported
constructors, mismatched captures/installations and incomplete required coverage.
The structured snapshot must pass its independent admission before any source
association can be used. Diagnostic locations are never an authority.

The consumer fixes the source interpretation, installed catalog and exact admitted
original independently of a proof method or companion. Its result names its
supported source fragment, all accepted source declarations/instances, the exact
admission and the source-to-program connection proposition. An unsupported form
or an incomplete association produces no connection theorem. The enclosing
receipt reports the missing link; the frontend cannot replace it with native
`status: checked`.

## Checking judgments

The checker reconstructs these judgments from authored facts. Existing exported
bindings and candidates are search accelerators: deleting one may make checking
slower or incomplete, but cannot make a different program correct.

| Judgment | Required reconstruction |
| --- | --- |
| Names and imports | Lexical binders, module/interface scope, visibility and imported notation environment; selected provider and canonical declaration are distinct. |
| Static instances | Declaration telescope, ordered actual terms, capability/natural requirements and associated-type reduction under the fixed installation. Callback/domain identities and capture partitions come from the instance contract, not decoded symbol hashes. |
| Runtime types and resources | Exact input/output type, nominal constructor identity, copy/drop rules, mutable state and scoped captures. A matching printed type is insufficient. |
| Protocol placement | Declared roster order, service owner, data availability, injective call substitution and custody. Omitted senders resolve from the current payload; receiver or later code cannot select them. |
| Effects and ordering | Pure versus ordered binding, reached guard/stop, random draws, messages, calls, query occurrences and loop boundaries in authored evaluation order. |
| Local inference | Omitted loop roster uses the active enclosing roster; a literal count may supply its maximum; eligible binders may supply sites. Written omissions remain absent in the AST. |
| Formal contract | Owner versus audit attachment, clause namespaces, resolved relation and request meanings, mandatory postconditions, exact ghost arguments and clause scope. None is inferred from an arbitrary Lean theorem name. |
| Lowering | Every executable source action has its admitted operation expansion; every admitted observable operation belongs to that expansion or an explicitly checked inserted-operation rule. |

The last judgment is bidirectional coverage. It prevents a compiler from dropping
a source action, adding a message or draw, reordering queries, weakening a guard,
or accepting a changed implementation just because the final returned value has
the expected type. Pure administrative operations may normalize only under the
installed rule and its proved semantics. There is no catch-all rule for an
unassociated row. Repeats check their count, maximum, participant set, carried
state and body; call expansion checks the actual callee and substitution.

## Neutral representation and evidence

Formal authored nodes use typed named fields (`formal.specification`,
`formal.ensures`, `formal.request`, applications, arguments, custody and binders).
They contain no parser-kind names or token arrays. Ordinary written types,
patterns and expressions retain the same role across grammar replacement.

A local binding proposal gives exact written use/binder addresses. A declaration
lookup gives provider/target and all exact-span candidates; candidates do not
select an occurrence. A closed-instance record fixes its template, ordered
static/scoped/domain substitutions and capture partition. `instance_rows` and
`rows` associate these proposals with the *same* admitted structured snapshot.
The checker validates those edges; it never joins independent artifacts by a
coincidentally equal name, ordinal or span.

Further accelerators may be added as typed proposal fields with exhaustive
reader changes. They cannot choose the observation relation, delete a mandatory
obligation, insert an unregistered law, or change the fixed goal. No native
checker transcript or success bit is acceptable evidence for its own soundness.

## Ownership and closure

The frontend maintains the schema, producers, hostile export controls, examples
and source-level inference rules. Lean implements source semantics, independent
checking and its soundness theorem against this contract. IR owns structured
admission and realization. Runtime owns execution and its installation. Their
identities and required links are listed in the [contract register](../contracts.md).

Current native export/comparison checks publication consistency and actual IR;
they do not prove the general source-elaboration judgment. Until Lean admits a
fragment and proves its checker sound, `source.correspondence` and applicable
exporter assumptions remain explicit. Supporting a new grammar does not restart
this contract or require Lean to interpret the retired native elaborator.
