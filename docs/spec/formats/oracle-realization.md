# Oracle realization record

`zkc.oracle-realization/0` describes one complete prepared module's oracle
realization. Its inputs are the immutable prepared original, a separate actual
common module, the requested realization policy and the record. The native
reader checks them together; a record cannot authorize its own policy.
The record is not executable code, a claim of prior admission, a proof of oracle
simulation, or permission to publish a proof artifact. Joint execution retains
this checked edge through compilation; logical-contract transport and native
proof integration remain separate obligations.

The policy chooses ideal data or a named Merkle scheme and leaf layout for each
base input/send occurrence. All choices use ordinary references and immutable
stores for table oracles. Virtual anchors are never committed. The same
module-wide reader accounts for every oracle-bearing entry and every preserved
ordinary declaration. It accepts no compatibility version or alternate schema.

The private checked owner consumes a prepared original and retains that original,
the actual candidate and the reader-checked serialized record together. Its
inspection APIs return independent module clones. Mutating an inspected clone
cannot change the owned edge or confer checked status on the mutation. An empty
oracle inventory uses the same reader and preserves the ordinary module exactly.
Joint compilation projects a private copy of the checked candidate, reads the
native schedule against that candidate's interface and retains the entire edge
in the final compilation owner. Execution does not authorize logical claim
publication; the complete logical-contract interpretation remains required.

Compilation selects explicit deployment entries after full source admission and
checked application expansion. Internal protocol declarations do not acquire
external oracle ingress solely because they remain in the source module.
Selection keeps the full authored source in the preparation owner, preserves
all non-program declarations, and refuses dangling symbolic references. The
selected output entry and every companion required by a polynomial
correspondence report are retained. Whole-module realization APIs continue to
realize the caller-supplied module; they do not infer deployment roots from
visibility or call-graph degree.

## Requested selection

The compiler, CLI and SDK use one requested selection, encoded as
`zkc.oracle-selection/0`. It is an input to compilation, never proof-supplied
policy or evidence of realization correctness. The object has exactly
`format`, `roots`, `order` and `authentication`.

`roots` is one of two exact tagged objects:

- `{"kind": "uniform", "table": {"scheme": S, "grouping": G, "order": O}}`
  selects the same table implementation for every actual base occurrence.
- `{"kind": "exact", "entries": [...]}` contains the complete ordered or
  unordered caller inventory. Each entry has exactly `entry`, `path`, `scheme`,
  `grouping` and `order`. Normalization uses source order, not supplied order.

`S` is an exact scheme identity or the empty string for ideal tables. `G` is
`individual` or `antipodal-pairs`; `O` is `natural` or `bit-reversed`. Ideal data
requires individual/natural layout. Selection-level `order` is `unrestricted`
or `after-final-draw`, and `authentication` is `per-query` or `atomic-blocks`.
The default selection is uniform ideal data, unrestricted order and per-query
authentication. Empty exact inventories are distinct from uniform selections.

The request admits no unknown/duplicate keys, aliases or alternate shapes.
Bounds are 1 MiB, 32 JSON nesting levels, 100,000 exact selectors, 64 path
ordinals and 4,096 bytes per name or scheme. Path ordinals are canonical
unsigned integers and each path is nonempty. A selected implementation must be
installed for every actual kind; no field or commitment substitution is implied.

`--oracle-realization=JSON` passes this object to executable compilation. The
same option is available through the source compiler, CLI and SDK settings.
It is not an elaboration or source-check option. Project settings carry the
same typed `oracle-realization` object. The selected request is part of the
compiler cache key and the exact packaged compiler options; a child invocation
inherits the actual request. The package's `options.oracle_realization` field
is mandatory, including for the default and an empty oracle inventory. This
changes the development version-0 package schema; no six-option compatibility
reader is admitted. The six existing Boolean options retain their meanings.

The realization record always carries the expanded exact choices, even when
the request used a uniform selector. The independent reader derives expansion
from the frozen prepared source and the independently supplied request. It does
not accept the record's root inventory as selection authority.

## JSON envelope and limits

The root has exactly these fields:

| Field | Meaning |
|---|---|
| `format` | Exactly `zkc.oracle-realization/0` |
| `selection` | Normalized caller-requested roots, query order and authentication boundary |
| `types` | Canonical complete source type descriptors, interned in first-use order |
| `entries` | Oracle-bearing entries in original declaration order |
| `declarations` | Complete actual declaration order and symbolic reference slots |

Parsing admits unique decoded object keys, valid Unicode and canonical unsigned
JSON integers. Missing or unknown fields, fractional/negative numbers, duplicate
or unused interned types, and out-of-range references refuse. The byte ceiling
is 32 MiB, JSON nesting is at most 64, the type table has at most 4096 entries,
and metadata traversal is bounded by one million object/array units. These are
representation limits, not additional logical oracle validity premises.

The selection is `{order, authentication, roots}`. `order` is `unrestricted` or
`after-final-draw`; `authentication` is `per-query` or `atomic-blocks`. Query
ordering and authentication granularity are separate choices. No `flush` alias
is admitted.
Each root row is `{entry, path, scheme, grouping, order}` in original declaration
and constructor order. `grouping` is `individual` or `antipodal-pairs`; `order`
is `natural` or `bit-reversed`. An empty scheme requests ideal data and requires
individual/natural layout. Virtual constructions have no selection row.

The caller selects either one table realization for every base root, or an
exact root inventory. The default uniform choice is ideal data with the
individual/natural layout. A uniform choice is expanded against the actual
prepared source; it never catches an unsupported scheme or kind by selecting
ideal data. An exact inventory must cover every base input/send occurrence
exactly once; missing, duplicate and extraneous selectors refuse. Paths must be nonempty and
have at most 64 ordinals; at most 100,000 root selectors are admitted. The reader
normalizes this external request against the original, checks actual bodies
under that request, and compares the entire record to its rederived encoding.
The JSON selection is descriptive, never an alternative source of authority.
Both policy choices are part of that comparison; root construction alone establishes
no query scheduling or batching property. For `after-final-draw`, both emission
and independent readback check the frozen prepared source: on every participant's
reached continuation, no random-service query follows that participant's logical
oracle query. Every service method (including `draw` and `index`) counts; there
is no implicit exemption for a private or undesignated service. This is a
participant-relative property, not a global ordering of independently running
participants.

The analysis distinguishes normal and stopped continuations, resolves actual
constants and invariant captures, and conservatively joins unknown outcomes
and loop counts through the checked bound. Another participant's guard or
completion cannot end this observer's continuation. Applications must already
be expanded with their role substitutions. A virtual query inherits its outer
query event; unused virtual declarations do not create events. One cumulative
100,000-step analysis budget covers all entries and observers, with at most
64 nested blocks. Unsupported or over-budget analysis refuses the policy.

The property permits per-query authentication. It authorizes no batching,
request hoisting, deferred authentication,
public-coin claim or simulation theorem. Those require their own checked
realization obligations. The record cannot override a failed source analysis.

A data type reference is an unsigned index into `types`. Each spelling must parse,
decode to an MLIR logical type and encode back exactly. Entry `interface.inputs`
and `interface.outputs` use data type references for data ports and
`{"service": installed_contract}` for random-service ports. A service identity
is not a data type, binding operand or native handle. The complete interface,
including each service's identity and singleton owner, is rederived from the
actual source signature; a record cannot supply or substitute it. Oracle kinds are objects
`{kind, arguments}`. An argument is `{kind: "type", value: type_index}` or
`{kind: "nat", value: unsigned_integer}`. Readers derive and check associated
Data, query, answer and named shapes through the closed kind contract.

## Entry records

Every entry has exactly the following fields. No field may supply arbitrary
operations, executable operands, literal values or helper bodies.

| Field | Meaning |
|---|---|
| `entry` | Original common function symbol |
| `merkle` | One `{position, commit, open, authenticate}` helper tuple per constructor; all four null for ideal and virtual constructors |
| `input_shapes` | `{anchor, port}` mappings from original root inputs to appended native shape inputs |
| `controllers` | Role/kind/access selections and complete controller metadata |
| `allocators` | Constructor order, then role order; each cell names its allocation helper |
| `locals` | Names of source-derived ordinary local recipes, in recipe order |
| `remotes` | Source-ordered receiver/holder controller indexes and all dynamic query helpers |
| `batches` | Source-ordered root occurrence groups and their aggregate helpers |
| `result_stores` | `{constructor, role, port}` mappings to native support outputs |
| `result_references` | `{result, role, stores}` mappings from original handle results to support ports |
| `constructors` | Source-derived construction inventory and per-role store layouts |
| `occurrences` | Source-derived generated common sites and their purpose/role/path |
| `query_blocks` | Ordered logical query paths and the source-derived packet capacity |
| `interface` | Complete native input/output type references and role families |
| `logical_interface` | Original oracle input/output pairings, distinct from native representation leaves |
| `contracts` | Complete original clause inventory and exact statement selections |

Each constructor records `constructor` (`input`, `send` or `virtual`), `path`,
`kind`, `holder`, ordered `receivers`, `site`, `declaration`, `scheme`,
`maximum_instances` and `roles`. A role layout is `{role, fields, record, store}`;
its ordered fields are `{name, type}`. Paths are instruction ordinals in the
prepared entry, descending through repeats; they are not JSON array addresses
in the written or structured source exports. The scheme is empty for ideal
selections and always empty for virtual anchors. The original fixes custody and all types.

An occurrence is `{site, purpose, role, path}`. The interface has `inputs`,
`outputs`, `input_roles` and `output_roles`; role lists keep original order.
Original input and result positions remain fixed. An ideal root input becomes
Data. A Merkle root input becomes the selected scheme's commitment type. For a
dynamic table, one index input is appended per original root port, in ascending
original-port order, with that port's receiver role family. `input_shapes` binds
that index to the original anchor; a fixed extent needs no new input. Protocol
admission requires exactly one binding for each raw root input. Neither a root
nor holder Data supplies the receiver's expected extent.

A holder checks its own Data and shape, commits it and retains Data plus private
opening state. A send delivers only the root. A receiver checks its own expected
shape, including the selected layout's positive power-of-two premise, and stores
that shape with the root. Input construction does not equate the supplied root
with a commitment to the holder's Data. Query authentication uses that same stored root and expected shape.

Appended support stores are native representation leaves, distinguished from authored results by the result maps.
They do not establish a general logical-handle codec or cross-entry graph ABI.

The logical interface is `{inputs, outputs}`. Each list follows original anchor
port order, with rows `{data, anchor, type, holder, receivers}`. Port numbers
refer to the original common signature; `type` uses the complete logical type
schema, including a bounded sequence's maximum. This replaces the former bare
`kind` field in version 0; producers, exact readers and fixtures change together.
There is no alternate legacy row shape.
Input rows bind the exact root data and handle leaves. Result rows choose the
first unused matching holder-data leaf in result order, under the same component
view/application and role rules as Protocol admission. Repeated aliases still
have distinct paired data ports. The original remains the source of authority;
record rows cannot substitute same-typed holder or receiver components.

This layout records associations, not equality between role components or a
cryptographic interpretation of a clause. Returned references connect to actual
support stores through `result_references`; they are not serialized Data values.
Logical anchor-clause transport still requires its typed interpretation before
native proof publication can accept that profile.

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

## Common opening communication

All remote queries use bounded dynamic demand windows. A receiver controller's
base constructors must select Merkle realizations at one remote holder. They
may have different answer kinds, installed schemes and allocated instances, and
may occur in recurrent virtual graphs. The common region must include the
holder. Mixed local/remote bases and selection across holders refuse with
`oracle-common-communication-profile`. This is a realization capability bound,
checked over the complete controller inventory, rather than a restriction on
logical oracle formation or an implicit switch to ideal data.

The planner derives remote receiver/holder pairs and source batch coordinates
from the frozen prepared original. The reader first checks actual controllers,
Merkle helpers and allocators, then derives that same schedule. A remote row
contains exactly `{receiver, holder, demand, response, open, packet, window}`.
`receiver` and `holder` index the entry's controller inventory. Each receiver
appears once, in first source-use order. `open` names an ordinary private scoped
helper with signature `(request, holder stores...) -> response`; the request,
response, constructor dispatch and store order are derived from checked source
models, never accepted as record overrides.

The other remote fields have these exact schemas. Types use the shared intern
table; helper fields use actual candidate symbols.

| Object | Exact fields |
|---|---|
| `demand` | `frame`, `sequence`, `state`, `initialize`, `advance`, `consume` |
| `response` | `answer`, `authenticate`, `resume` |
| `packet` | `request_sequence`, `response_sequence`, `answer_sequence`, `groups_sequence`, `key`, `key_sequence`, `group`, `open`, `authenticate` |
| `window` | `request_sequence`, `answer_sequence`, `capacity`, `collect`, `replay`, `finish` |

`demand.state` is an ordered type vector. Its header retains constructor,
instance, position, answer kind, continuation and phase; the final field is an
append-only frame sequence. Each frame retains parent constructor, instance,
position, next child and parent continuation. Discovery has no answers or
fabricated answer indices. It follows actual constructor instances and
nonadaptive position maps in depth first source order, preserving duplicate and
unused queries. It checks every node's domain before descent, including empty
virtual nodes. A false predicate retains a pending domain cut and prevents
later discovery; it does not execute a stopping source guard ahead of prior
authentication.

`response.answer` is ordinary private variant data, with one typed logical
answer alternative per exact base constructor. `authenticate` consumes one
retained request and its response, reads that request's own receiver stores and
checks its exact constructor, root, expected shape, layout and position. It
returns a typed answer without resuming. `resume` checks the evaluator's actual
request identity and resumes using its own continuation coordinates. Neither
helper establishes authority for an arbitrary caller-supplied association.

`packet.group` computes first-use physical groups at runtime. A key is the
exact source constructor, instance and selected physical leaf. Equal roots or
Data never merge different anchors. Logical order and multiplicity remain in
the request sequence and one group ordinal per occurrence. The key and group
sequences are ordinary private data. `packet.open` opens each physical request
once through the checked `open` helper. `packet.authenticate` checks sequence
lengths and the complete logical-to-physical association, then authenticates
every logical occurrence independently against its retained request. Physical
sharing never authorizes sharing authentication. All answers return together
after the whole logical sequence authenticates. No packet helper resumes an
evaluator.

## Checked query batches

`per-query` selects one root occurrence per batch and packet capacity one.
`atomic-blocks` selects up to 32 consecutive queries whose actual references
and positions are available before the first query and whose checked transport
inventories agree. Different root answer kinds and continuation layouts remain
controller-local. Every intervening non-query operation ends a batch, including
service draws, guards, calls, completion and control flow. An answer-dependent
position or handle ends the current batch before that dependency. Unknown
positions remain eligible: demand discovery preserves the valid prefix and
replay executes a pending domain failure after that prefix authenticates.
An upper shape bound is never proof that a queried position is valid.

Each `query_blocks` row is exactly `{queries, packet_capacity}`. `queries` lists
source occurrence paths in order, retaining repeated references and positions.
`packet_capacity` is null for ideal local evaluation; otherwise it is the same
positive entry-wide bound used by every remote window and packet helper.
For `atomic-blocks`, this is the maximum source-derived structural leaf bound
of any selected batch, with a minimum of one. It is a packet limit, not a new
source-domain premise. A bound of 1048576 or greater refuses. Capacity exhaustion
refuses the selected realization rather than silently changing the policy.
There is no `request_groups` field or fixed nominal packet compatibility route.
Actual physical groups are runtime data checked by the packet reader.

Each `batches` row is exactly `{remotes, body}`. `remotes` is the ordered list of
indexes into the entry's remote inventory, one per source root occurrence;
repeated indexes retain distinct occurrences. `body` has exactly
`{demand_state, evaluator_state, request_sequence, answer_sequence, collect,
replay, finish}`. State vectors concatenate each selected root's state in source
order. Request and answer sequences and the immutable ordered store types must
agree across roots. All helper signatures borrow scope and return explicit
outcomes, and must fit native source execution's width limit of 512.
The batch reader consumes windows already independently checked by its caller.

The common body initializes demand and evaluator states with each root's exact
source reference and position and binds the actual immutable stores. The batch
`collect` helper traverses root windows in order, carrying one request sequence
and a blocked flag. It returns all updated demand states, that sequence and
one unsigned end offset per root. End offsets retain empty and repeated ranges.
Normal discovery does not evaluate answers. On an empty positive round,
`collect` finishes every root on its original evaluator state in source order
before rejecting an impossible successful empty round. The first actual source
failure propagates before that internal guard, and no empty packet is sent.

For a nonempty round, the common body calls the actual packet grouping helper,
sends the physical requests, dispatches the holder opening, receives responses
and authenticates the ENTIRE collected logical prefix before any replay.
The actual two group outputs must come from the same call. The complete common
body reader checks source operand identity, state/store captures, ordered helper
calls, exchanges and SSA dataflow; recording a correct unused helper cannot
substitute for checking the actual call.

Batch `replay` passes each root the same request and answer sequences and its
exact contiguous range: zero to the first end, then the previous end to the next
end. The last end must equal request length. Each root matches its next evaluator
request to the retained constructor, instance, position and kind, then resumes
with its own continuation. Discovery's pending domain cut is executed by the
original evaluator guard after the preceding authenticated prefix. Earlier
authentication failure therefore precedes a later source-domain failure.
Replay neither authenticates nor releases source answers. After the structural
rounds, batch `finish` finishes every root in source order and releases the
complete answer tuple only after all roots succeed. Zero-total batches skip
collect and communication and invoke this finish once, retaining empty-node
domain and answer checks.

Structural leaf counts govern positive common rounds. The holder opens the
actual received sequence without knowing receiver-private positions in advance.
Role assembly supplies availability, not component agreement. A failed batch
releases no source answer and reaches no later batch. `atomic-blocks` explicitly
selects the whole packet observation boundary, including when an early
authentication fails; it does not promise the same failure trace as `per-query`.
Multi-holder routing remains unsupported.

### Generated failure relation

The logical request-prefix comparison assumes successful execution of generated
discovery, carrier and replay work, apart from the source domain checks and
selected authentication failures being compared. Generated native failures are
separate outcomes: reference lookup, position computation, storage growth,
opening, message decoding, authentication, answer computation and retention can
stop at their actual positions in the generated program. They do not promise
the same request prefix or resource trace as a per-query implementation.

The checker covers these outcomes by checking complete actual bodies and their
fixed failure continuations. A failed helper is not caught and reclassified as
a source-domain cut, a partial packet is not published, and no alternate
realization is retried. An arbitrary all-stop candidate does not satisfy that
body comparison. Honest successful execution additionally needs the selected
provider assumptions, valid source inputs and sufficient native resources.
These native structural checks establish neither a Lean simulation theorem nor
a cryptographic authenticity or resource-trace equivalence theorem.

## Controller metadata

Each controller is `{role, kind, access, body}`. Access is `available` or `holder`;
the body repeats and must agree with the same role and access. The body has:

- `capacity`: `{leaves, nodes}`, independently derived from the original;
- `kinds`, `answers`, `state`, `stores`: ordered kind/type inventories;
- `constructors`: `{source, role, kind, first_continuation, lookup, functions}`;
- `continuations`: `{constructor, query, record, sequence, previous_kinds}`;
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
continuations and actual anchor reads. Answers accumulate in append-only,
kind-indexed sequences. Each frame stores ordinary indices into those sequences;
`previous_kinds` is the ordered kind inventory re-derived from preceding source
queries. The state header retains the most recently produced answer index.
Returning to a virtual parent reads each child's own index from its kind's arena
in source query order. The reader checks those actual SSA references, arena
appends and loads; a record's kind or index claim cannot authorize substitution.
The evaluator remains responsible for source-ordered domains and answers.
Dynamic demand windows use its checked request/resume transitions only after
complete prefix authentication; answer arenas do not grant independent
permission to defer domain checks or change the selected observation policy.

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
