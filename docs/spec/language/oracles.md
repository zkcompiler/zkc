# Oracle source projection

Oracle handles retain a holder, an ordered logical identity and a receiver
family. They are not ordinary shared data or a Merkle commitment. The
[Protocol IR contract](../ir/protocols.md#logical-oracle-kinds-and-handles)
owns their meaning; realization selects an implementation separately.

This page distinguishes the implemented layout projection from the remaining
virtual-definition design. It does not announce production source-format cutover.

## Types and ports

Installed type representations use the same constructors as the retained
source profile. Ordinary library aliases may give them convenient names:

```zkc
type Table<T: Type + Copy + Drop> = builtin("oracle.table", T)
type Fixed<T: Type + Copy + Drop, rows: nat> = builtin("oracle.table", T, rows)
type Oracle<K: OracleKind> = builtin("oracle", K)
type Vector<F: Field> = builtin("vector", F)

pub protocol Read<F: Field, N: nat> roles(P, V)(
    word: Oracle<Fixed<F, rows = N>> @P -> V;
    position: index @V
) -> F @V:
    answer <- query word at position
    return answer
```

The holder arrow is required on oracle ports and forbidden on ordinary data.
The holder cannot also be a receiver. Ordinary role resolution, active-roster
checks and placement inference apply. A query is an ordered event, including
when its answer is unused or its position repeats. A query position must be
available at the selected receiver. No query is inserted by a pure expression.

Dynamic table ports have a named shape bound:

```zkc
#[shape(word.rows, bound = Maximum)]
pub protocol ReadDynamic<F: Field, Maximum: nat> roles(P, V)(
    word: Oracle<Table<F>> @P -> V; position: index @V
) -> F @V:
    answer <- query word at position
    return answer
```

The attribute selects exactly one custody input or output and one installed
dimension. The current table kind has `rows`. Unknown ports or dimensions,
duplicate bounds, a bound on a sized port, and an unsized port without a bound
refuse. The maximum is a static natural; the anchor retains its actual shape.
An attribute does not add an independent shape port or assert a range theorem.
Written source retains the attribute's target, dimension, bound and span;
checked port metadata contains the resolved maximum.

The draft's common `table<F, rows = N>` / `table<F>` convenience family still
needs the shared catalog type-constructor adapter. The two explicit aliases
above exercise the existing installed representations without introducing an
ad hoc optional-static-argument rule.

## Delivery and views

```zkc
word <- send values from P to V as oracle<Fixed<F, 16>>
dynamic <- send values from P to V as oracle<Table<F>>(rows = count) max Maximum
answer <- query word at position
values_at_holder = oracle.data(word)
count_at_family = oracle.rows(word)
unsized = oracle.forget_rows(word)
```

Delivery specifies the holder explicitly and permits comma-separated receivers.
Its data must be available at that holder. A sized kind supplies the row count;
an unsized kind requires both the shared actual count and a static maximum.
No maximum is narrowed to a signed integer. Ordinary `send value to V` retains
its existing sender inference and single-receiver semantics.

`oracle.data` exposes data only at the holder. `oracle.rows` exposes the shape
to the handle's family. `oracle.forget_rows` preserves anchor and family while
forgetting a static dimension in the type. These are fixed source operations,
with positional operands and no method lookup. Both `oracle.name` and
`oracle::name` select that same reserved operation family. Unknown operations,
wrong arity, extra static parameters and named operands refuse.

## Bounded sequences

```zkc
empty = oracle.empty<Fixed<F, 16>, 4>() @(P, V)
words <- oracle.append(empty, word)
count = oracle.length(words)
selected <- oracle.at(words, position)
answer <- query selected at row
```

The empty sequence's role tuple gives holder first, followed by receivers.
Append and selection are ordered checked operations. Selection requires its
index to be available to the whole family; it cannot let each receiver choose
a different anchor. Appended handles must preserve kind and custody family.
The static sequence capacity is independent of each table's row shape.
Sequences remain internal protocol values under the current IR profile.

## Protocol boundaries and components

An oracle port is one logical source value. Calls and returns lower it into
holder data and receiver anchor with the existing `oracle_components` operation;
the callee rejoins those components using `oracle_input`. The same ordinary
call-site role substitution applies, including when the callee uses different
role names. Actual-body comparison checks the selected components and ordering.
Authors do not write an additional decomposition operation or acquire a freely
constructible anchor. `oracle.data` is the explicit holder-only data view.

```zkc
pub protocol Relay<K: OracleKind> roles(A, B)(
    word: Oracle<K> @A -> B
) -> Oracle<K> @A -> B:
    return word

// In a caller whose roster is (P, V):
received <- Relay(word) @(P, V)
```

Restricted logical records are a separate aggregate extension. Their eventual
field projection must retain typed field paths and component custody. Ordinary
tuples, records and native collections continue to exclude handles; the ABI
decomposition above does not make them ordinary serializable values.

## Virtual definitions: designed integration boundary

`oracle def` declares a query function, and `value <- Definition(...)`
instantiates it. The query suite is nonadaptive: positions depend on the query
parameter and immutable ordinary captures, never on a preceding answer. Its
answers use total mathematics. Calls to checked local index arithmetic, random
services, sends, guards and arbitrary local helpers cannot enter that suite.
Repeated or unused source queries remain ordered occurrences.

The frontend projection must produce a typed immutable query plan containing:

- Resolved source-handle ports, then ordinary captures, followed by the query
  parameter, with exact kind-associated query and answer types.
- The named result shape, its initial ordinary index parameters and static
  bounds; source custody and ordinary availability remain distinct.
- The checked mathematical helper closure, ordered source-query sites and
  resolved admissibility predicate declaration.
- The authored predicates and their required obligation keys, even if no
  security bundle was requested.

`requires` inside an oracle definition contributes to that admissibility
predicate. It is neither an executable guard nor permission to put a partial
operation inside total mathematics. Each construction creates an obligation
for the actual anchors and captures. The generated predicate is fixed before
companion lookup, through the existing [companion contract](companions.md).
No separate source keyword for an admissibility certificate is needed.

Instantiation allocates a fresh anchor but does not query the source or
materialize all answers. Its captures must be available at the holder and every
receiver. After a challenge exchange, authors can assemble those components
explicitly with `@(P = received, V = sampled)`; assembly asserts no equality.
The IR verifier owns dependency/shape formation, and the actual-body comparison
must inspect the complete definition and predicate, including unused ones.

This projection remains refused until its typed plan, total query-domain maps,
obligation export and independent actual-definition comparison are implemented
together. A parser-only declaration is insufficient. The existing IR per-query
virtual evaluator does not fill these frontend obligations automatically.

## Setup and realization selection

Setup association and realization selection belong to a closed deployment,
separately from the logical protocol and its specification. Setup selectors
must obey the existing [entry association rules](entries.md#setup-associations):
typed input paths, no overlap, whole setup-bearing leaves and Host authorization.
They do not create keys or discharge setup correctness. A realization request
must identify the exact closed source subject, kind, implementation suite and
required observation/authentication policy. Selection consumes the IR owner's
checked policy and cannot be inferred from an oracle type alias.

The layout deployment projection is deferred with the entry/proof integration;
the current C++ realization-selection API remains its producer. A future CLI or
project-file spelling must serialize that same policy. Introducing a second
inline policy language before the existing reader and Host setup contract are
connected would duplicate authority. KZG acceptance therefore needs an installed
polynomial-evaluation kind, checked setup selectors and a KZG realization, while
Merkle table acceptance needs no setup key. Neither is supplied by parsing
`Oracle<Kind>`.

## Coverage and integration gates

| Logical operation | Layout producer | Current boundary |
| --- | --- | --- |
| `oracle_input` | Custody input port | Implemented projection |
| `oracle_send` | `send ... as oracle<...>` | Implemented projection |
| `oracle_query` | `query handle at position` | Implemented projection |
| `oracle_contents` | `oracle.data(handle)` | Implemented projection |
| `oracle_shape` | `oracle.rows(handle)` | Implemented table dimension |
| `oracle_forget_shape` | `oracle.forget_rows(handle)` | Implemented table dimension |
| `oracle_sequence_empty` | `oracle.empty<Kind, Capacity>() @(Holder, Receivers...)` | Implemented projection |
| `oracle_sequence_append` | `oracle.append(sequence, handle)` | Implemented projection |
| `oracle_sequence_at` | `oracle.at(sequence, position)` | Implemented projection |
| `oracle_sequence_length` | `oracle.length(sequence)` | Implemented projection |
| `oracle_virtual` | `oracle def`, followed by ordered instantiation | Parsed design; typed definition/instantiation integration pending |
| `oracle_components` | Implicit decomposition at oracle protocol calls and returns | Implemented projection; no additional author keyword |

Virtual definitions require the complete integration contract above. They must
not be approximated by precomputing a table, copying an anchor, or flattening
custody into shared availability. General FRI query-domain maps additionally
depend on the [catalog design](../../compiler/query-domain-maps.md). Polynomial
evaluation kinds and KZG realizations require their own installed kind and
realization contracts; changing the source alias cannot provide them.

Every source operation uses the existing checked native operation, source
comparison and IR verifier. This does not prove source elaboration, oracle
realization correspondence, extraction or privacy. The shared FRI/STARK
acceptance scenario records those owner results separately in the
[contract register](../contracts.md#shared-oracle-stack-acceptance-boundary).
