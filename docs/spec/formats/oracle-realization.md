# Oracle realization record

`zkc.oracle-realization/0` describes one complete prepared module's oracle
realization. Its inputs are the immutable prepared original, a separate actual
common module, the requested realization policy and the record. The native
reader checks them together; a record cannot authorize its own policy.
The record is not executable code, a claim of prior admission, a proof of oracle
simulation, or permission to publish a proof artifact. Joint execution retains
this checked edge through compilation; logical-contract transport, native proof
integration and complete Merkle query realization remain separate obligations.

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

## JSON envelope and limits

The root has exactly these fields:

| Field | Meaning |
|---|---|
| `format` | Exactly `zkc.oracle-realization/0` |
| `selection` | Normalized caller-requested roots, query order and authentication boundary |
| `types` | Canonical ordinary logical type spellings, interned in first-use order |
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

The caller's absent root inventory explicitly selects ideal data everywhere.
A present inventory must cover every base input/send occurrence exactly once;
missing, duplicate and extraneous selectors refuse. Paths must be nonempty and
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

The property permits the existing immediate authentication at each reached
query. It authorizes no batching, request hoisting, deferred authentication,
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
| `locals` | Names of source-derived common local recipes, in recipe order |
| `result_stores` | `{constructor, role, port}` mappings to native support outputs |
| `result_references` | `{result, role, stores}` mappings from original handle results to support ports |
| `constructors` | Source-derived construction inventory and per-role store layouts |
| `occurrences` | Source-derived generated common sites and their purpose/role/path |
| `query_blocks` | Ordered logical query paths and their physical request groups |
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

The immediate-query profile admits multiple remote base constructors at one
holder in the receiver controller's inventory. Constructors may use different
answer kinds and installed Merkle schemes, allocate multiple instances, and
participate in recurrent virtual graphs. The enclosing common regions must
already include the holder. Mixed local/remote bases and selection across holders
refuse with `oracle-common-communication-profile`. This is a realization
capability restriction, not a restriction on logical oracle formation or an
implicit switch to ideal data. The profile is conservative over the controller's
whole constructor inventory, not a claim of per-query reachability precision.

A query initializes its controller from the actual reference and position and
advances it before opening communication. A Request-phase suspension produces
one request record with ordered fields `(constructor, instance, position)`.
The holder dispatches the actual constructor, rejecting an unknown tag, loads
that instance's private opening state and shape, and opens it. Its response is a
closed variant with one `ConstructorN` alternative per source constructor; each
payload is the complete row followed by its proof. Request and response each
use one ordinary exchange. Their nominal descriptors retain the source entry,
receiver, holder and ordered constructor inventory, and obey ordinary variant
limits, including at most 32 response alternatives.

Before reading an anchor or using a response, the receiver's selected arm checks
that the suspended phase is Request, that its constructor equals the response
alternative, and that its answer kind is the expected kind. It loads the root
and expected shape through the **suspended reference**, authenticates at the
**suspended position**, and resumes with the original five request/continuation
coordinates. An untrusted response cannot select a different anchor, position or
continuation, including when constructors have identical payload types and roots.

Holder dispatch and receiver authentication/resumption are specialized scoped
helpers. A separate reader checks their actual conditional/match bodies,
resolved helper identities, ordered guards and SSA operands. The common-body
reader checks the request construction, exchanges, stores and continuation calls.
There is one route for single and multiple constructors; there is no new runtime
oracle object, wire opcode or general-purpose local recipe language. These
native checks establish correspondence to the selected recipe, not a Lean
simulation theorem or a cryptographic authenticity theorem.

When virtual constructors are present, the queried handle must already be
available at both receiver and holder. Each role computes the structural leaf
count from its own component and immutable stores; role assembly supplies the
counted loop's pointwise count. Assembly establishes availability, not component
agreement. No extra count message exposes later work before it is reached.
Without virtual constructors, a base query has exactly one leaf and needs no
holder-side handle. The loop carries receiver-only controller state and captures
the appropriate role stores. It advances after every authenticated answer,
including the last, before finishing the outer query. Thus an invalid later or
zero-query virtual child retains the prior opening prefix but prevents the outer
answer. Zero structural leaves perform no opening exchanges. Duplicate and
unused virtual queries remain separate reached openings. This reached-prefix
route also handles queries for which the fixed-block proof below is unavailable.
Multi-holder routing and general virtual batching remain unsupported.

## Checked atomic query blocks

`per-query` retains one logical query per block. `atomic-blocks` admits a local
block of at most 32 consecutive base-table queries with the same receiver and
holder. Every intervening non-query operation closes the block: this includes
service draws, guards, completion, calls, control flow and answer-dependent work.
A missing proof closes the block and retains the ordinary singleton route.

Before crossing a query-domain check, the planner and reader derive its validity
from the actual prepared source. The supported evidence is an index literal
within the exact table extent, or a successful same-owner `index` service query
with a literal positive bound no larger than that extent, or a reached
same-participant `data.index_less` guard proving that bound before the actual
query. The successful-point profile checks exact SSA identity and dominance;
merely computing the Boolean supplies no premise. The extent is static
or the literal actual `rows` operand of a send; a shape upper bound is not an
extent. Role restrictions, shape forgetting and invariant repeat captures
preserve the underlying source identity. Loop carries, sequence selections,
virtual admissibility laws and unchecked computed indices supply no such proof.
This restriction preserves the reached request prefix at an invalid query.

Each `query_blocks` row is `{queries, request_groups}`. `queries` lists all
logical source paths in order, including duplicates. `request_groups` is either
an equally sized list of physical opening slots, numbered in first-use order,
or `null` for ideal evaluation and dynamic virtual enumeration. A shared slot
requires the same actual source anchor and constructor, the same selected layout
and the same physical leaf. Equal roots or equal Data do not merge anchors.
The supported sharing proofs use identical position SSA values or literals
mapped through the checked layout, including antipodal pairs and bit reversal.
The entire block partition and slot mapping are rederived, not trusted metadata.

A fixed block emits one request exchange and one response exchange. A singleton
uses the ordinary request/response component directly. Larger packets are
ordinary nominal Records whose ordered payloads are those components. Scoped
`exec.variant` and `exec.match` helpers pack and unpack packets, retaining their
outcomes and charges; proof values do not become mathematical data. The nominal
packet identity is `["zkc.oracle.query-packet/0", purpose]`, where purpose is
`opening_request` or `opening_response`. Existing type, variant and codec limits
apply. An independent reader checks the actual helper bodies and ordered fields.

Every logical query authenticates its selected response against its own
suspended root, shape, constructor and position. All authentications dominate
all source answer releases and subsequent continuation work. A failed block
releases no source answer and reaches no later block. The complete request
packet is observable even if the first authentication fails: `atomic-blocks`
selects that observation boundary explicitly, rather than promising equality
with per-query failure traces. Physical sharing reduces transmitted openings;
authentication is currently repeated for each logical query. Resource limits
and native failures remain those of the generated program. This correspondence
check is not a resource-trace equivalence, simulation theorem or authenticity
proof. General virtual/FRI batching requires additional checked shape and
position evidence.

### Generated failure relation

The logical request-prefix comparison assumes successful execution of generated
discovery, carrier and replay work, apart from the source domain checks and
selected authentication failures being compared. Generated native failures are
separate outcomes: reference lookup, position computation, storage growth,
opening, message decoding, authentication, answer computation and retention can
stop at their actual positions in the generated program. They do not promise
the same request prefix or resource trace as a per-query implementation.

The checker covers these outcomes by checking the complete actual body and its
fixed failure continuations. A failed helper is not caught and reclassified as
a source-domain cut, a partial packet is not published, and no alternate
realization is retried. An arbitrary all-stop candidate does not satisfy that
body comparison. Honest successful execution additionally needs the selected
provider assumptions, valid source inputs and sufficient native resources;
the stop-permitting correspondence alone does not establish it.

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
The current controller still authenticates and evaluates one request at a time.
Answer references prepare bounded virtual batching without authorizing delayed
domain checks or changing the current observation policy.

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
