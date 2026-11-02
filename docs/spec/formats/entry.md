# Entry interface and package

This is a native contract. See the [language contract index](../language/README.md)
for source rules and the [runtime reference](../../runtime/README.md) for usage.

## Retained interface

`zkc.language-interface/0` has exactly these JSON members: `format`, `capture`,
`original`, `toolchain`, `entry`, `protocol`, `protocols`, `relations`, `job`,
`setups`. `protocol`
selects one symbol from `protocols`. Every original protocol and relation appears
exactly once. Unknown tags, missing members and extra members refuse.

A run `job` has only `kind: "run"`. A proof job has exactly `kind: "proof"`,
`prover`, `verifier`, `public`, `acceptance`, `completion`, `target` and
`construction` and `gates`. The required `gates` array contains exact `{path,
bits}` objects: nonempty source-identifier paths and integer difficulties, as
defined by the [authored gate contract](../language/entries.md#proof-declarations).
An empty array selects no gates. Roles are original source roster names;
`public` is a sorted
array of exact objects `{port, path, role}`. `port` is the logical input ordinal,
`path` is the ordered schema-field path, and `role` is the verifier's source
name. Entries are strictly ordered by port then path, with no duplicates or
ancestor overlap. Each selects ordinary verifier data, including empty values;
together they cover every verifier ordinary input, including setup-initialized
verifier-key fields. Whole logical selections
refuse; ordinary subtrees remain selectable. Native proof public inputs remain
the derived increasing original native-index vector. Acceptance uses the
selector format below. Completion is either
a producer Boolean output selector or JSON null. Target is a clause name or JSON null. An authored
construction has `kind: "authored"` and `format`. A native construction has
`kind: "fiat_shamir"`, `format`, `suite` and `services`, a singleton array of
logical service indices. A programmable construction has `kind: "derived"`,
`format`, `suite`, `services` and `symbol`. Its suite is a managed transcript
identity or null for a local root; its symbol names the checked construction.
Its service array is nonempty and strictly increasing. Every selected service
belongs to the verifier. Query domains follow their actual service contracts,
independently of a programmable provider's domain. Unselected services remain
explicit participant inputs.

Format is `zkc.framed/0` or `raw.bytes/0`; native shorthand requires framing.
A programmable record codec uses raw bytes. Independent reading checks these
choices against the original signature, selected construction closure and
native statement, including its exact `target` clause-name reference. The
selected clause's decision role must agree with the verifier and acceptance
selector; equal output indices alone do not establish that agreement. Source
comparison separately checks that these choices match the selected checked Entry.

`setups` is an array of records with exactly `name` and `inputs`. Each input
selector has exactly `port` and `path`, using logical input and product-field
indices. Native slices are derived from the checked schema. Readers check exact
coverage, nonoverlap, nonempty selections and proof-key availability. Source
comparison additionally binds slot names and selector choices to the checked
Entry. Setup metadata is part of authenticated package bytes. Setup association can
split selectable product fields; an ordinary single-operand variant or native
collection remains indivisible and still requires its supplied value, including
when its active alternative is empty. Verifier-key initialization requires an
exact builtin key selection.

Each protocol record has exactly `symbol`, `roles`, `inputs`, `outputs`,
`services`, `clauses` and `common_input_requirements`. The last member is always
required, including an empty inventory. There is no compatibility default.
A port has exactly `name`, display `type`, logical
`index`, ordered absolute protocol input/result indices in `native`, recursive
`schema`, `placement` and `components`. Only a direct `oracle` or
`oracle_sequence` port additionally requires `maximum_rows`: null for a sized
kind, otherwise a canonical uint64 decimal string. Aggregate logical ports
reject this member. Zero-storage ports retain their complete schema and
placement with empty native/component arrays.

`common_input_requirements` contains exact common-control admission equivalence
classes. Each record has exactly `components` and `observation`. Each component
has exactly unsigned bounded `input` (source input ordinal), source roster name
`role`, and `path`, an array of exact `{kind,index}` objects. Kinds are `field`,
`alternative`, `payload`; every alternative is immediately followed by a payload.
For example:

```json
{"components":[{"input":0,"role":"P","path":[{"kind":"field","index":1}]},
               {"input":0,"role":"V","path":[{"kind":"field","index":1}]}],
 "observation":{"kind":"value"}}
```

Field indices select declared fields, including zero-storage fields. Payload
indices select declared alternative fields, independently of their flattened
native offsets. Nested payload selections retain every enclosing alternative.
A path ends at exactly one ordinary component. Logical handles, custody,
zero-storage values and aggregate products cannot become invented common inputs.
Ordinary children of distributed products use the existing component map at
their actual roles, including below an enclosing custody prefix. Their selected
Data facet and custody authority remain separate. No native coordinate, inferred
type or diagnostic span is serialized in this inventory.

Observation is exactly `{"kind":"value"}`, `{"kind":"tag"}` or
`{"kind":"extent","axis":0}`. Value requires Copy data; tag requires a variant
and establishes no payload equality. Extent requires Copy collection data and
retains its original container type and exact axis, independently of contents.
Supported axes follow the [input-binding contract](input-bindings.md). Conditional
alternative paths do not project or compare inactive payloads.

Each class has at least two distinct roles and one exact resolved logical type
and observation. Components sort by input ordinal, lexicographic typed path
(kind order field, alternative, payload; then index), and role ordinal. Classes
sort lexicographically by their complete component arrays and then observation
(value, tag, extent with axis). Independently derived equalities normalize into
full connected classes, so chain and star derivations agree. Distinct nominal
types and conditional coordinates do not merge through equal storage. Duplicate,
nonmaximal or reordered serialized classes/components refuse; readers do not
repair them. There are at most 1,024 classes, 32,768 components in total, and
32 source path steps, further narrowed by type depth and cumulative work limits.
Readers bound these structures before indexing, sorting or projection.
Source publication and source comparison each use their enclosing inventory
allowance across retained Protocols. Derivation setup, layout observation,
nested semantic queries and canonicalization debit that same allowance,
including work performed before an error. A per-Protocol observer cannot
restart or independently spend the enclosing allowance.

These inventory bounds are owned by Frontend / Language. Their units are
classes and components per Protocol, path steps per component, and work units
of the enclosing allowance, which is the invocation's `Limits::work` (by
default 32,000,000) shared with the rest of publication, comparison or
reading. The compiler's source publication, source comparison and independent
reader refuse each bound, including exhaustion of the enclosing allowance
during the inventory step, with `source.limit` "common inventory limit
exceeded". The SDK reader enforces the class, component and path bounds and
refuses with `entry-interface-limit`.

The source producer derives from each immutable closed concrete Protocol and its
actual helper closure. Independent C++ reading derives the original native
requirements through native common-control analysis and compares the exact
mapped inventory for every retained Protocol, including helpers. Source
comparison independently replays every concrete declaration's source inventory.
Host packages retain these inventories in their nested Protocol packages.
Self-hashing a replacement package establishes neither source correspondence nor
inventory completeness: those require the trusted compiler boundary. External
context authentication and actual value admission belong to the SDK/runtime;
interface metadata establishes no physical execution or proof support.

Every schema has exactly these common members: `kind`, `identity`, display
`type`, `generated`, `custody`, `sealed`, `constructible`, `permissions`, `roles`, `element`,
`leaves`, `fields` and `alternatives`, with the kind-specific oracle members
below. `generated` is required-nullable: null for ordinary source families,
otherwise the lowercase 64-digit generated-family identity binding capture,
installation, target and family. It is distinct from the static type `identity`. Retaining it lets independent
readers reproduce the full schema hash without dropping its generated-family
binding.
`custody` is an unsigned bounded JSON integer prefix count, never a Boolean.
An ordinary explicit wrapper has one custody leaf; a distributed wrapper has
one per declaration role, in telescope order. `roles` contains declaration-order
role parameter names only for nominal distributed records, at most 1,024, the
catalog limit `record.roles`; other schemas have an empty array. The brace-profile alternative below, which the
[contract register](../contracts.md#current-producers-and-consumers) records under recursive record placement, also has an empty
array. These names are definition metadata, not protocol participants.
`element` is required-nullable and non-null exactly for a fixed array, including
length zero. Every expanded array field has that complete element schema.

A field has exactly `name`, body `offset`, Boolean `public`, required-nullable
`placement` and child `schema`, plus conditional `maximum_rows` below.
Alternatives have exactly `name` and payload `fields`. Offsets include the whole
custody prefix and count each handle once. Distributed record fields require
placement formulas in their declaring record's role telescope, after static
specialization. Ordinary fields, alternative payloads and expanded structural
fields require null, as do fields of the brace-profile alternative.
Private and zero-storage fields remain in declaration
order. Privacy is part of schema consistency and identity; the independent
reader does not reconstruct lexical home authority for internal source clauses.
Source comparison checks that authority. External setup/input selectors require
public accessible paths.

`sealed` is a required Boolean independent of custody and constructibility;
nonnominal schemas require false. Retained nominal declarations and source
comparison authenticate sealing. External ordinary supply validates sealing,
privacy and construction at every ancestor. Retained typed transport can pass a whole
ordinary value under its export policy without constructor authority. This grants
no public SDK projection or external assembly through sealing or private fields. Equal identities require
equal complete authority metadata, including private and empty children.

`constructible` is a required Boolean for construction of the outer value.
External byte input additionally requires construction authority throughout the
selected schema, including a zero array's element template. `permissions` is
the canonical ordered subset of `Copy`, `Drop`; `Copy` requires `Drop`.
Transparent products intersect child permissions; explicit restrictions can
remove permissions. Logical products and handles are not ordinary byte-input
constructors.

Placement is exactly one of:

```json
{"kind":"data","roles":[0,2]}
{"kind":"oracle","holder":0,"receivers":[1,2]}
{"kind":"product","instance":"<schema.identity>","arguments":[1,0],"fields":[]}
```

All role values are integer ordinals in the owning protocol roster, or the
owning declaration telescope for a field formula. Data roles and oracle
receivers are nonempty increasing distinct sets; a holder is outside its
receivers. Product arguments are injective and every child participant belongs
to that application. A nominal product preserves telescope order and arity;
its fields follow declaration order. Applying its role substitution to every
field formula must reproduce the port child placements exactly. Product
`instance` equals the corresponding external schema `identity`; hashing that
already external digest again is invalid. Internal kind-framed type identities
are converted once at the producer boundary.

Structural tuples with logical children also use product placement, with one
child per position. A logical fixed array uses exactly one element-placement
template even at length zero; schema fields still expand its physical extent.
Its template position is not a selected physical element index. Structural
arguments are the canonical union of child participants, including the phantom
element template of a zero array. Schema-aware substitution restores this
canonical union while retaining nominal telescope order. Structural products do
not gain nominal constructor or home authority. Ordinary availability for a
structural Product is the intersection of its children's ordinary role sets,
including a zero-array element template. The participant union grants no
whole-value access. Selected target statements and witnesses use this same
exact intersection for verifier visibility.

Each component has exactly `path`, `leaf`, `role`, `facet` and `native`. Path is
a declaration-field ordinal array, including physical array indices; `leaf` is
the local terminal or custody-prefix leaf ordinal. Facet is `data`,
`oracle_data`, `oracle_anchor` or `custody`. Order is declaration traversal,
then body leaf, then increasing participant. Native coordinates are absolute in
the owning protocol input or result signature. Shared ordinary data and receiver
anchor families can repeat a native coordinate; uniqueness is over
`(path,leaf,role,facet)`. Readers reconstruct complete coverage, order, exact
types, role attributes, bounds and ABI selections independently from schemas,
placements and actual native signatures. Producer component arrays grant no
additional authority. A port role union cannot authorize a field selection.

An oracle schema has kind `oracle` for a singleton handle or `oracle_sequence`
for a bounded handle sequence. Both have no data `leaves`, fields or
alternatives, zero custody, false constructible, empty declaration roles, null
element, and permissions `["Copy", "Drop"]`. Both additionally require
`oracle: {kind, arguments}` and recursive `data_schema`. Closed kind arguments
are ordered pairs `["type", <canonical BoundType>]` or
`["nat", <canonical uint64 decimal string>]`. The current kind is `table`, with
a row type and optional exact row count. An `oracle_sequence` additionally
requires canonical uint64 decimal-string `maximum`, including zero. This exact
capacity is independent of row count and per-element row maximum. Other kinds
reject `maximum`. Singleton data schema is `K::Data`; sequence data schema is
`sequence<K::Data>`, retaining the outer sequence even if the associated data is
itself a sequence.

A direct unsized handle field requires canonical decimal-string `maximum_rows`;
sized handle fields and all other fields omit it. Each handle body leaf expands
to holder data followed by its receiver anchor family: `[K::Data, Oracle<K>]`
or `[Sequence<K::Data>, OracleSequence<K,M>]`. Each nested handle owns its own
holder, receivers and row bound. Actual input bindings and output component
operations must retain the exact pair, order, roles and bounds.

The `logical_record` kind is a nominal distributed product, including an empty
product. It retains its telescope, formulas, private fields and restrictions,
with no aggregate native `leaves` or alternatives. Tuples and arrays derive
logical category recursively, including a zero array's element. They likewise
have no aggregate data carrier. Ordinary records, variants, associated
representations and builtin generic carriers cannot hide logical children.
Ordinary schema leaves include their custody prefix; recursive body width for
logical products includes their custody count and one body leaf per handle.
Repeated type identities must agree on the complete schema, including privacy,
formulas, generated family, element, capacity and associated data.

While the brace source profile remains supported, its telescope-free
`#[logical]` record has one explicit alternative in this current schema:
`roles` is present and empty, every field `placement` is present and null,
permissions are exactly Copy and Drop, custody is zero, and constructibility is
false. At least one direct handle or sequence is required; zero capacity counts.
Every other child must recursively be ordinary shared data. Nested logical
metadata and restricted wrappers are excluded. Each use has a product placement
whose direct handles share exactly one holder and receiver set, whose ordinary
children all have that family's complete data-role set (including empty fields),
and whose arguments are the canonical sorted family union. Private fields,
sealing, nominal identity, row bounds and independent component reconstruction
remain mandatory. This is not a missing-member fallback or permission to read
historical encodings. Remove this alternative and the source Layout migration
seam together when the brace parser retires; final 4.1 records always declare
their role telescope and field formulas.

Selectors retain the existing direction/port/path/role format. A named role
selects ordinary data only when every selected leaf is a data component at that
role. An anchor selector has null role and selects one singleton handle's anchor,
with its associated data schema and its own implicit holder; sequences and whole
logical products are not anchors. External projection through custody and projection through opaque types
refuse. Internal checked-source clauses may observe ordinary Copy payload fields
through custody for specification bookkeeping; this creates no executable field
value and discharges no resource obligation. Native expansion comes from independently checked components rather
than aggregate role unions or body offsets. Setup coverage and proof-key/public
policy likewise inspect each actual data component. Public selections cover ordinary verifier subtrees. Handles, oracle holder data,
anchors and custody are separate obligations; none is ordinary public byte data.
Coverage uses semantic field/role atoms independently of physical native slots.
A supplied ordinary child does not authorize assembling its parent.

Internal protocol ports may carry checked logical records, handles and sequences;
preparation eliminates these internal ports. Rust metadata inspection validates
the retained closure structurally without importing or executing its logical
handles. Complete transparent distributed roots containing only admitted ordinary
components can enter through checked ordinary selections. Outstanding sealed,
hidden, custody, handle or origin obligations refuse; ordinary holder data does
not create a handle. Root outputs expose admitted ordinary views, without an
ordinary logical-value decoder. Realization determines the public commitment and
witness interface before executable input admission; this source interface does
not itself grant a data codec. Source names, display text and schema identities
still require the separate source-correspondence check.

There is one strict current `/0` shape, with required-nullable members and
unknown/duplicate-key rejection. The recursive record fixture and consumer
handoff are in [the interface fixtures](../../../compiler/test/fixtures/language-interface/README.md).
Rust and independent Lean readers must migrate to this exact shape, including
role-qualified public selections and sealing, before
landing. Fixture admission does not establish a correspondence theorem or
complete new formal proofs.

### Source names and native correspondence

Source names in `entry`, participant rosters, ports, services, clauses, setup
slots, fields and alternatives follow the
[Unicode identifier profile](../language/lexical.md). Canonical qualified names
join admitted segments with `::`. Display `type` strings describe types and
are not identifier or equality authority. Symbols are native encoded identities.

The interface preserves original NFC UTF-8 source names, including ASCII names.
Native correspondence is derived only from authenticated ordered rosters:
participant index `i` uses `role` followed by eight lowercase hexadecimal digits,
setup index `i` uses `setup` with the same width, and alternative index `i` uses
`case` with the same width. Ordinals start at zero. Count and uniqueness are
checked first. Readers compare the resulting labels with the actual native
artifact; no caller-supplied renaming table is authoritative. Selectors and proof
roles carry source names and are translated through these rosters. Logical
alternative names and native variant labels are checked in the same order.

Declaration symbols use `s` followed by decimal UTF-8 byte length, `h` and
lowercase byte hex for each source path segment, including ASCII segments.
[Translation](../language/translation.md#source-and-native-names) owns this
encoding, its expansion bound and specialization policy. Notation descriptors,
lexical scopes and source occurrences are diagnostic data and do not add fields
to this interface.

### Relations and logical schemas

A relation record has exactly `symbol`, `static_arguments`, `inputs` and
`definition`. `static_arguments` is a required ordered list of the closed typed
terms in the [protocol origin grammar](structured-source.md). It retains every
opaque static parameter, including unused parameters, with its type, natural
decimal spelling and domain identity. The list permits at most 128 arguments,
4096 aggregate term nodes and 64 term levels; recursive lists permit at most
512 children and term strings at most 512 UTF-8 bytes. Formula and captured
relations require an empty list. Opaque identity is the native declaration's
`(kind, key, revision, static_arguments)`; ordered argument trees are part of
identity. The C++ reader compares this list with the original declaration.
The Rust Host validates the typed carrier and retains its exact arguments; it
does not reconstruct MLIR declarations or assign opaque predicate meaning.
The authenticated package binds the original IR hash and compiler-checked
interface bytes.
Each formal has `name`,
`purpose`, ordered `native` indices and `schema`. Definition records have exactly
`{kind, function}` for a formula, `{kind}` for an opaque declaration, or
`{kind, asset}` for a captured R1CS, AIR or bundle, with `kind` spelled `r1cs`,
`air` or `bundle`. Their identity triple comes from the actual native
declaration. Formula kind is `zkc.language.formula/0`, key is the closed relation
symbol, and revision is a lowercase SHA-256 representation digest. Its material is
length-framed in this order: kind, predicate helper symbol, decimal logical input
count, each full logical schema digest and purpose, decimal transitive helper count,
then each helper symbol and definition digest, sorted by symbol. A definition digest
hashes framed `zkc.language.formula-helper/0` and canonical generic MLIR without
locations. Frames use unsigned 64-bit little-endian lengths. The closure includes
the root; shared helper definitions are hashed once per immutable checking phase.
Printing pins every flag, disables hex output and uses elision thresholds above
admitted payload sizes, independent of process-global MLIR flags.

The full schema digest hashes length-framed byte strings in this exact order:

1. `zkc.language.schema/0`, textual kind, static nominal `identity`, then the
   non-null `generated` digest if present (no frame for null).
2. Decimal custody count, sealed, constructible, Copy and Drop (the latter four use
   `0` or `1`); decimal role count and declaration-order role names.
3. `element` and its full child digest when present, otherwise one empty frame;
   then `data_schema` and its full child digest when present, otherwise one empty
   frame.
4. Decimal body leaf count and declaration-order leaf descriptions. Ordinary
   leaves contribute their canonical native spelling, including custody units.
   A handle contributes `oracle`, kind identity, each kind argument's canonical
   spelling, and decimal sequence capacity or an empty frame for a singleton.
5. Decimal field count and ordered field descriptions; then decimal alternative
   count, each alternative name and its field count/descriptions.

Each field description contributes name, decimal body offset, public (`0` or
`1`), `placement` followed by the formula frames below or one empty frame for
null, then `maximum_rows` and decimal bound if present (no frames when absent),
then the child's full schema digest. Formula frames are: `data`, decimal role
count and each role; `oracle`, holder, receiver count and each receiver; or
`product`, external instance digest, argument count and arguments, field count
and recursive child formulas. Every count, offset, role and bound uses canonical
unsigned decimal text. Hash framing uses unsigned 64-bit little-endian byte
lengths. Display type spelling is excluded from the digest but remains subject
to repeated-identity consistency and checked-source comparison. These digests
bind metadata and printing policy, not semantic equivalence.
The formula helper name is `zkf_` followed by lowercase SHA-256 of the bytes
`zkc.language.predicate:` concatenated with the native declaration key. Its JSON
link must equal the original relation's explicit `formula` symbol reference.
Canonical source emission uses the derived name; structural original admission
resolves the exact retained reference without reconstructing it from the key.
Native formula admission requires a private,
nonempty body with the declaration's signature and no executable references, then
checks polynomial observations on bounded detached clones using the original
helper table. The supplied original is unchanged; limits remain `source.limit`
and invalid observations are `target.admission` with source attribution.
Captured kinds are `zkc.relation.r1cs/0`, `zkc.relation.air/0` and
`zkc.relation.bundle/0`, with canonical asset identity as key and `0` as
revision. The reader requires the matching immutable admitted asset handles,
supplied outside this small JSON. For a bundle it derives the formal list from
the admitted bundle, as the
[protocol contract](../language/protocols.md#bundle-declarations) defines, and
requires the record to spell exactly that count, each purpose, each logical
kind and each single native leaf. A Bundle used only in a relation declaration
is retained in the package's `assets` member. The Rust interface reader checks
the digest and single-leaf structure; Entry admission then independently derives
the formal purposes and exact field, Boolean, index and vector types from the
packaged Bundle. A mismatch returns `entry-asset-relation`. This checks the
declaration's meaning without evaluating its predicate or proving that the
protocol's acceptance implies it.

Each clause has `name`, `kind`, `subject`, `residual` and `decision`; absent optional
fields are JSON null. An application has a relation symbol and ordered `operands`.
Selectors have `direction` (`input` or `output`), logical `port` index, field-index
`path` and actual `role` name (or null for the singleton anchor case above).
Native slices are derived from the admitted logical
schema, rather than supplied again. Relations compare exact logical identities.
Clauses remain on closed component declarations; original `protocol.apply`
occurrences own their operand/result and role mappings. There is no separate
serialized application graph.

The original `protocol.func` owns the complete native clause inventory.
`readInterface` independently flattens each logical selector through its admitted
schema and requires exact agreement with that inventory, including kind, name,
relation, direction, port, role, residual and decision. Omitting, adding or moving
a clause in the interface cannot change the original declaration's contract.

The standalone `readInterface` API admits original MLIR and checks the interface
against its exact byte hash, selected protocol, flattened types and participant
roles. It checks contiguous port/field indices, complete native coverage, variant
labels/payloads, custody prefixes and managed-service contracts. Logical types
with the same identity must have consistent kind, label and schema. Kinds are
`boolean`, `index`, `field`, `group`, `unit`, `tuple`, `array`, `record`, `logical_record`, `variant`,
`associated`, `builtin`, `oracle` and `oracle_sequence`. Ordinary scalars have
their matching single native leaf; unit has none. A `builtin` schema's single
leaf is a catalog source-data type constructor without its own source kind
(every source-data row except `bool`, `index`, `field` and `group`) whose catalog
permissions are Copy and Drop. Interface leaves carry ordinary data, so affine
managed state, such as a transcript, is never a leaf and refuses with
`source.interface`. Tuples/arrays have positional
fields, with one common element identity
including the zero-length element template. Records have identifier fields; associated representations
have exactly one `value` field. Only variants have alternatives. An empty product
cannot hide data leaves. Custody belongs only to nominal kinds, including distributed records.

`identity` is the lowercase SHA-256 digest of the closed
[canonical source type key](../language/definitions.md#nominal-authority) used by
nominal custody and variant descriptors. It includes static arguments,
including phantom and zero-length array element types, and the defining source
authority of every nominal they name. The key encodes the type kind tag,
symbolic flag, length-framed domain, then, for a record, logical record, variant
or module node that names a declaration, the framed authority (64 lowercase
hex, or empty for a generated declaration), then the normalized dimension, the
argument count and recursively framed argument keys; a natural uses its kind tag
and framed normalized dimension alone. Tags follow `Type::Kind`; framing is an
unsigned decimal byte length followed by `:` and the exact bytes. The toolchain
identity fixes this encoding. Equal paths from different source revisions have
different identities. Native custody carries the exact digest; a variant
carries `["zkc.language", lowercase_hex(full_preimage)]`. The preimage is the
complete original UTF-8 type key. Both C++ and Rust readers require even-length
lowercase hex, check encoded expansion and decoded byte bounds before allocation,
validate UTF-8 and hash the decoded bytes. A chosen label or a digest in place of
the preimage refuses. The reader checks both anchors. Over a retained
declaration carrier, the C++ reader recomputes each retained nominal's identity
from its term and the carrier's authority rows, and requires a null authority
exactly for a schema with a non-null `generated`. Other source type identities
remain source assertions until checked against the retained project. `type` is display text, never equality authority.
An empty array's element meaning is bound by its identity and source agreement;
no selectable element field is invented for it. Copy, Drop and
external construction authority cannot exceed children or native leaves. Opaque
associated schemas cannot be externally constructible. Multi-participant ports
require Copy and native participant admission for every leaf. Concrete codecs
remain independently checked by message and Host input admission.

`compareInterface` checks the decoded view against the retained source layouts,
ports, services, relations and clauses. It independently checks the clause inventory
against immutable templates and captured `spec` block/clause spans and tokens.
Omitting a clause and its predicate together cannot satisfy source correspondence.
This check does not replace native admission or the source-to-original SSA check.
`admitOriginal(entry, original, interface)` performs formation, formula admission,
source-to-SSA comparison, structural interface decoding and source-interface
comparison on one parsed original. It then requires byte agreement with canonical
source emission for both original and interface, fixing declaration order, symbol
spelling and diagnostic locations. It retains those exact bytes and returns
`CheckedOriginal`. `prepareOriginal` emits and runs the same independent checks;
its emitted bytes need no second canonicality comparison.
`CheckedOriginal::interface()` exposes the checked view; `selectedProtocol()`
selects a protocol or proof deployment's protocol record. Application Entry
functions expose their checked Host interface and retained original SSA.
Host authentication must bind the retained interface bytes, not arbitrary caller JSON that happens to compare semantically.
The byte overload of `inspectApplications` admits the entire original and interface before calling a
read-only visitor for each static `protocol.apply`. Each occurrence exposes its
caller/callee records, actual MLIR operation, callee-to-caller role substitution,
and clauses bound to actual operand/result SSA values. Its path indexes operations
in the caller block and then enclosing `protocol.repeat` blocks. Repetition is one
static occurrence; runtime iterations and transitive calls are not expanded. This
keeps contracts on definitions and derives their uses from the original program,
without serializing another call graph. The operation, values and referenced views
are borrowed for the callback only. Visitor work is the caller's responsibility;
traversal and binding use the source work and nesting limits. Structural inspection
has the standalone reader's guarantees. The `CheckedOriginal` overload additionally
uses its retained source authority and captured assets. Selector paths cannot
project through associated representations, even when structurally copyable.

`checkInterface` compares decoded JSON against the retained original's
exact source interface. This binds source names, nominal schemas, permissions and
capture/Entry selection. The standalone structural view does not establish source
correspondence or constructor authority and cannot authorize private input decoding.
Both readers reject duplicate/unknown keys, unknown tags and malformed metadata.
Object member order is immaterial for semantic interface comparison; admission of
a published checked original requires canonical bytes. The original identity hashes exact MLIR bytes
without debug locations under a fixed printing policy. The toolchain identity binds
the installed catalog, compiler source build identity and actual LLVM/MLIR release.
Build identity includes the source-name profile manifest, generator and raw
hash-pinned UCD inputs.
The catalog uses `zkc.language-catalog` length framing. Kernel rows contain
their signatures and parameter contracts.
Source availability still requires an installed declaration at an admitted
authoring stage, with all applicable semantic-facet and source-effect checks.
The identities bind the checked environment; they are not an authenticity signature or
security claim. The independent comparison binds generated coordinates to source
spans; diagnostic paths do not affect capture or original identity.

External source-interface JSON accepts raw UTF-8 and equivalent valid JSON
escapes; admission uses the exact decoded name bytes without normalization.
Invalid UTF-8, unpaired surrogates and duplicate decoded keys refuse. Deterministic
output uses raw UTF-8 with required JSON escapes. Canonically sorted object keys
use UTF-8 byte order; arrays preserve their authenticated order. Schema identity
frames decoded names, while capture identity hashes exact authored source bytes.
Neither is redefined as a hash of arbitrary input JSON spelling. Published
original/interface bytes retain their canonical printing policy.

External interface JSON uses unique decoded object keys and canonical unsigned
decimal numeric tokens. Signed, leading-zero, floating and exponent spellings
refuse. Boolean and null tokens retain ordinary JSON grammar and remain subject
to the interface schema. Lexical limits apply before schema admission. External
input passes through the byte reader; an already decoded JSON value does not
retain its original numeric spelling.

The name encoding changes generated symbols and role/setup/case labels even for
ASCII source, so artifact and transcript bytes can change with the compiler.
These contracts remain version `0`: producers, readers and fixtures use one
current schema, with no legacy decoding path. Public source names and Entry JSON
keys are retained. Native contract/domain IDs, sites, assets and hashes keep their
existing ASCII grammars.

## Published Entry package

`packageEntry` accepts only an owned `CompiledEntry`. It emits `zkc.entry/0`
with exactly `format`, `original`, `interface`, `artifact`, `options` and
`assets`. Original MLIR, interface JSON and Host control artifact or native proof deployment are exact
strings. Child deployments inside a Host artifact retain their own exact packages. Options contain exactly the required JSON Booleans
`simplify`, `release_storage`, `fuse_vector_reductions`, `finite_bulk` and
`fuse_collect_fold` and `calculation_batching`. Finite bulk selection and calculation batching default
to true and both fusion choices to false; all four fields are required and independent of
generic simplification. Missing,
duplicate, unknown or non-Boolean option fields refuse. The job kind and complete
source interface remain in the retained interface, avoiding a second name or
participant table. Package SHA-256
covers the exact emitted bytes, including source capture, selected Entry,
toolchain, compilation options and assets. Complete Entry aliases can share
executable bytes while naming different packages.

For proof Entries, native artifact binding checks agreement between all five
package options and the deployment's ordered
[compiler choices](proof.md#deployment-and-invocation-records), as well as the
original and selected artifact identities. This remains one current version-0
schema; no shorter option record or compatibility reader is admitted.

`assets` carries the compiler-visible assets referenced by executable operations
or Bundle relation declarations. It is an array of pairs `[expected_sha256, body]`: the lowercase
SHA-256 of the body's canonical encoding and that exact canonical text. Every
body is a [`zkc.ring/0` arena](../domains/ring-expressions.md) or
[`zkc.relation-bundle/0`](../domains/relation-bundles.md). The compiler includes
every required body in strictly ascending digest order, so duplicates cannot
occur. The package names no asset paths or capture names; executable parameters
and relation definitions refer to canonical digests.
An empty array is the exact form when neither names an asset. The member
is required: a package without it is not `zkc.entry/0`.

The whole escaped package is bounded to 64 MiB; callers may lower this limit.
The original, interface and artifact retain their own component limits. Assets
number at most 256, each body is at most the arena's 8 MiB, and all bodies
together are at most 32 MiB. The Rust reader refuses a
descending or repeated digest, a digest that is not 64 lowercase hexadecimal
digits, or a pair of another shape with `entry-package-format`, and an
exceeded count or byte bound with `entry-package-limit`. Reading checks only
those bounds as a precheck on text; the Host admits each body and the
program's references when an Entry is admitted. The combined registries' charge
of canonical bytes plus decoded metadata is also bounded to 32 MiB, and can
refuse a package within the transport limit. The `language-package` command writes exact package bytes
without a trailing newline. Package identity is distinct from the original
identity used by native proof binding. A consumer must obtain its expected
package identity independently; internal hashes do not authenticate a supplied
package. Retaining MLIR does not require the Host to recompile it or establish
a security theorem.

## Host control artifact

An Entry function publishes `zkc.host/0` in the existing package artifact member.
It has exactly `format`, `original`, `entry`, `functions`, `calculations` and
`deployments`. `original` hashes the exact retained original; `entry` selects a
function symbol. The interface uses `selection: {kind: "function", function}` and
a `functions` signature inventory. Its `protocols`, `relations` and `setups`
arrays are empty: child native packages own those contracts.

Compiler publication and Rust admission bound the Host artifact to 16 MiB,
JSON nesting to 256 and lexical nodes to 800,000 before structural decoding.
The node ceiling is four times an interface document's, as its byte ceiling
is: a Host artifact restates each signature, block-argument and deployment
schema, so the generated wrapper of a Protocol selection grows by about 235
nodes per role. Its 1,024-role roster needs about 240,000 nodes with one port,
and about 369,000 with one port placed at every role.
The shared [node-ceiling fixtures](../../../common/tests/fixtures/entry-json/README.md)
give the interface document's and the Host artifact's node ceilings a case at
the ceiling and one past it, which the compiler's and the SDK's readers both run.
Scalar tokens have at most ten bytes. Embedded program and package strings
share the artifact byte ceiling; interface metadata retains its narrower string
limit. Duplicate decoded keys, invalid Unicode and noncanonical numeric tokens
refuse. The compiler may apply tighter source limits.

Each signature has `symbol`, ordered named `parameters` with a logical `schema`,
and one `result` schema. Schemas retain the same nominal, constructor, permission
and native leaf contracts as protocol interfaces. Each function has `signature`
and `body`. Blocks have ordered `arguments`, `operations` and `returns`; SSA
definitions have `id` and `schema`. IDs are unique within a function, and uses
must dominate their operations. Nested regions receive explicit arguments.

Host operations cover product/variant construction and projection, unpacking,
static Entry calls, numerical calculations, native invocations, if/match/for,
require, drop and explicit stop. Every potential region and static reference is
admitted before execution. Retained helpers form an acyclic static graph.
The retained original uses standard `func` and `cf` control with explicit
[Exec outcomes](../ir/execution.md). Ordinary nominal construction belongs to
Data. Every fallible call exposes a returned payload or terminal stop;
`exec.dispatch` propagates the stop through the actual CFG. The independent
reader checks the complete graph, actual operands and continuation arguments.
The compiler emits this original directly from the checked source. Functions
retain only ordered parameter names in `entry.parameters`; actual native ports
determine their schemas. Conditional and loop region captures are explicit block
arguments, including unused and repeated captures. Native reconstruction derives
the artifact from those operands, operations and control edges. It does not read
a stored body or signature document. The closed Host profile checks every block,
the exact unsigned loop condition and latch, and all stop/continuation edges;
arbitrary CFG restructuring requires a separately admitted reader profile.
The executable Host stop has no ordinary results and bypasses the suffix.
Operation argument/result signatures, complete variant coverage, region captures
and loop-carried values must agree; a reference cannot select a structurally
similar deployment with a different generated identity.

A calculation has `id`, ordered `parameters` and `results` schemas, a `function`
root and an exact `program` string. The existing physical `zkc.program/0` grammar
permits a nonempty Local function table with empty participant and entry tables.
Its full definitions and potential branches remain subject to native admission.
Only the selected Local root's dependencies are installed for execution.
Numerical fragments use the maintained mathematical realization, scheduling,
physical lowering and VM mechanisms. They do not introduce another arithmetic
interpreter or a synthetic participant.

A deployment has `id`, `operation` (`run`, `prove` or `verify`), ordered
`parameters` and `results` schemas, and an exact child `package` string. Child
source interfaces independently determine role-local ports, proof choices and
setup contracts. The parent package pin covers child bytes; native admission and
application authority are still required. Verification installs the verifier
closure without producer data, entropy or producer-only primitive support.

Compiler publication compares the complete Host original and executable against
the checked source, including numerical definitions and child closure. The Rust
Host independently checks structure, signatures, schemas, references and native
children after package authentication. Neither check turns a package digest into
a protocol security theorem. All schemas remain version zero; there is one
current grammar and no legacy source-run reader.

A protocol's default run uses its qualified protocol name in the public source
interface and the existing `function` package kind. Its generated Host function
calls the same joint child as an authored wrapper; it adds no package grammar.
An explicitly selected generic run appends its supplied static argument tokens
to the public name. This source selection label does not replace the canonical
typed identity of the closed computation or its generated nominal family.

A generated joint child uses `Protocol::run` as its internal Entry name. A closed
static specialization appends `_` and the lowercase SHA-256 of its canonical
closed family type, such as `module::Protocol<Field>`. Host admission checks this
identity against every generated nominal signature. Equal native port shapes do
not permit replacing a child with a different specialization.

## Oracle realization selection

Executable compiler options include mandatory `oracle_realization`, the exact
[`zkc.oracle-selection/0` request](oracle-realization.md#requested-selection).
It accompanies the six Boolean optimization options for every package, including
Host children and the default ideal selection. Unknown, missing or malformed
fields refuse; development version 0 has no prior six-field option reader.
The request participates in cache identity and is forwarded to both joint and
proof compilation. Choice metadata does not establish oracle correspondence.
