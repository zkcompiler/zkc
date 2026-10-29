# Oracle realization record

`zkc.oracle-realization/0` describes one complete prepared module's oracle
realization. Its inputs are the immutable prepared original, a separate actual
common module and the record. The native reader checks all three together.
The record is not executable code, a claim of prior admission, a proof of oracle
simulation, or permission to publish a proof artifact. Production integration,
logical-contract transport and Merkle realization remain separate obligations.

The current mode is `ideal`. It uses ordinary data, references and immutable
stores for table oracles. Virtual anchors are never committed. The same
module-wide reader accounts for every oracle-bearing entry and every preserved
ordinary declaration. It accepts no compatibility version or alternate schema.

The private checked owner consumes a prepared original and retains that original,
the actual candidate and the reader-checked serialized record together. Its
inspection APIs return independent module clones. Mutating an inspected clone
cannot change the owned edge or confer checked status on the mutation. An empty
oracle inventory uses the same reader and preserves the ordinary module exactly.
This ownership boundary does not yet authorize production projection or claim
publication; the complete logical-contract interpretation remains required.

## JSON envelope and limits

The root has exactly these fields:

| Field | Meaning |
|---|---|
| `format` | Exactly `zkc.oracle-realization/0` |
| `mode` | Exactly `ideal` |
| `types` | Canonical ordinary logical type spellings, interned in first-use order |
| `entries` | Oracle-bearing entries in original declaration order |
| `declarations` | Complete actual declaration order and symbolic reference slots |

Parsing admits unique decoded object keys, valid Unicode and canonical unsigned
JSON integers. Missing or unknown fields, fractional/negative numbers, duplicate
or unused interned types, and out-of-range references refuse. The byte ceiling
is 32 MiB, JSON nesting is at most 64, the type table has at most 4096 entries,
and metadata traversal is bounded by one million object/array units. These are
representation limits, not additional logical oracle validity premises.

A type reference is an unsigned index into `types`. Each spelling must parse,
decode to an MLIR logical type and encode back exactly. Oracle kinds are objects
`{kind, arguments}`. An argument is `{kind: "type", value: type_index}` or
`{kind: "nat", value: unsigned_integer}`. Readers derive and check associated
Data, query, answer and named shapes through the closed kind contract.

## Entry records

Every entry has exactly the following fields. No field may supply arbitrary
operations, executable operands, literal values or helper bodies.

| Field | Meaning |
|---|---|
| `entry` | Original common function symbol |
| `controllers` | Role/kind/access selections and complete controller metadata |
| `allocators` | Constructor order, then role order; each cell names its allocation helper |
| `locals` | Names of source-derived common local recipes, in recipe order |
| `result_stores` | `{constructor, role, port}` mappings to native support outputs |
| `result_references` | `{result, role, stores}` mappings from original handle results to support ports |
| `constructors` | Source-derived construction inventory and per-role store layouts |
| `occurrences` | Source-derived generated common sites and their purpose/role/path |
| `interface` | Complete native input/output type references and role families |
| `logical_interface` | Original oracle input/output pairings, distinct from native representation leaves |
| `contracts` | Complete original clause inventory and exact statement selections |

Each constructor records `constructor` (`input`, `send` or `virtual`), `path`,
`kind`, `holder`, ordered `receivers`, `site`, `declaration`, `scheme`,
`maximum_instances` and `roles`. A role layout is `{role, fields, record, store}`;
its ordered fields are `{name, type}`. Paths are instruction ordinals in the
prepared entry, descending through repeats; they are not JSON array addresses
in the written or structured source exports. The scheme is empty in ideal mode
and always empty for virtual anchors. The original fixes custody and all types.

An occurrence is `{site, purpose, role, path}`. The interface has `inputs`,
`outputs`, `input_roles` and `output_roles`; role lists keep original order.
Original result positions remain fixed. Appended support stores are native
representation leaves, distinguished from authored results by the result maps.
They do not establish a general logical-handle codec or cross-entry graph ABI.

The logical interface is `{inputs, outputs}`. Each list follows original anchor
port order, with rows `{data, anchor, kind, holder, receivers}`. Port numbers
refer to the original common signature; `kind` uses the kind schema above.
Input rows bind the exact root data and handle leaves. Result rows choose the
first unused matching holder-data leaf in result order, under the same component
view/application and role rules as Protocol admission. Repeated aliases still
have distinct paired data ports. The original remains the source of authority;
record rows cannot substitute same-typed holder or receiver components.

This layout records associations, not equality between role components or a
cryptographic interpretation of a clause. Returned references connect to actual
support stores through `result_references`; they are not serialized Data values.
Logical anchor-clause transport still requires its typed interpretation before
production projection can accept that profile.

The `contracts` object has exactly `clauses` and `statements`. Clauses follow
original declaration order and contain `kind`, `name`, `subject`, `residual` and
`decision`. A subject or residual is `{relation, operands}`, with the exact local
relation symbol; absent residuals and decisions are JSON null. A selector is one
of `{component: {direction, port, role, type}}` or
`{anchor: {direction, port, pair, kind}}`. Directions are `input` or `output`;
`type` uses the shared type table, and `kind` uses the kind schema. The `pair`
index selects the corresponding input or output in `logical_interface`; it does
not select a participant's data as the anchor's meaning. Decisions use the
component object's fields directly and must name a Boolean output.

Statement rows are `{operation, target}`. `operation` is the zero-based operation
ordinal in the original entry block. `target` is the exact named target's clause
index or null for an unnamed statement. Equal relation/selector/decision tuples
do not merge distinct named targets. The original fixes the complete statement
binding and relation declarations, which the actual-body reader also preserves.
These fields are rederived by Protocol's shared bounded contract reader, not
accepted as producer-supplied predicates. Recording an anchor selector does not
supply its native predicate adapter. Rewritten oracle entries have neither
`contracts` nor `protocol.statement` on their native signatures: the frozen
original and this complete record retain those logical declarations instead.
Ordinary siblings retain their clauses and statements unchanged. The actual-body
reader refuses additional clauses or statements in a rewritten candidate.
Two originals can select different named targets yet produce identical native
code; their records still differ. A standalone executable candidate therefore
carries no authority to publish either original logical claim. Production claim
publication must consume and interpret the complete checked edge.

## Controller metadata

Each controller is `{role, kind, access, body}`. Access is `available` or `holder`;
the body repeats and must agree with the same role and access. The body has:

- `capacity`: `{leaves, nodes}`, independently derived from the original;
- `kinds`, `answers`, `state`, `stores`: ordered kind/type inventories;
- `constructors`: `{source, role, kind, first_continuation, lookup, functions}`;
- `continuations`: `{constructor, query, record, sequence, previous_answers}`;
- helper slots `leaf_counts`, `row_counts`, `construction_counts`, `initialize`,
  `advance`, `finish`, `resume`, `evaluate` and `contents`.

A helper slot contains a symbol string, or `null` only where the source-derived
recipe requires absence. Constructor `functions` has `queries` and `answer`.
Each ordered query is `{source, site, kind, position}`. Function and binding names
are references to actual declarations, never substitutes for checking bodies.

Pure position/answer helpers follow a closed substitution recipe derived from
the original: actual helper returns determine dependencies, all required total
operations retain their order and attributes, and each query answer remains a
distinct formal even if unused. Extra arithmetic and alternate helper indirection
refuse, including implementations that compute an equivalent result. Scoped
controller bodies separately check ordered domain guards, state transitions,
continuations and actual anchor reads.

## Declaration and reference slots

A declaration row is `[symbol, references]`. Rows preserve actual declaration
order, including retained originals. Each reference row is
`[operation_ordinal, attribute_name, symbols]`; the ordinal is a preorder walk
inside that declaration, starting at zero. Each symbol is an array containing
its root followed by nested references. Attribute traversal preserves MLIR's
attribute order. This table fixes generated and retained symbol spelling,
outlined-helper links and binding selection without encoding an executable body.

The reader resolves record symbols only inside the separately admitted candidate.
It derives layouts and common recipes from the original, checks actual SSA and
every helper body, verifies the complete declaration inventory, then independently
recomputes all derived fields and reference slots. Renaming a binding and all its
uses still requires a matching record. Unused declarations cannot hide outside
that inventory. Source locations and textual SSA names are not semantic record
choices; this is not a serialization of MLIR's textual formatting.

The private native checker establishes this structural correspondence. It does
not establish the independent Lean realization bridge, commitment security,
logical-clause transport or correspondence of later optimization passes. See
[protocol oracle semantics](../ir/protocols.md#logical-oracle-kinds-and-handles)
and [implementation status](../../status.md).
