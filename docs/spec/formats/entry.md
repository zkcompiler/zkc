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
`construction`. Roles are original source roster names; `public` is a sorted
array of logical input indices. Acceptance uses the selector format below. Completion is either
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
Entry. Setup metadata is part of authenticated package bytes.

Each protocol record has `symbol`, `roles`, `inputs`, `outputs`, `services` and
`clauses`. Each port has `name`, display `type`, `roles`, logical `index`, ordered
native leaf indices in `native`, and recursive `schema`. A schema has `kind`,
`identity`, display `type`, `custody`, `constructible`, `permissions`, `leaves`,
`fields` and `alternatives`. Fields have `name`, leaf `offset` and child `schema`; alternatives
have `name` and payload `fields`. Zero-leaf ports retain empty native indices.
Offsets are relative to their product or alternative payload. `constructible` is
a required Boolean for construction of that outer value. External input also
requires construction authority for every nested field and alternative payload;
packing already typed values does not fabricate their contents. Zero-length
arrays retain their element construction policy despite having no fields.
`permissions` is
the canonical ordered subset of `Copy`, `Drop`; `Copy` requires `Drop`.

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

A relation record has `symbol`, `inputs` and `definition`. Each formal has `name`,
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

The schema digest hashes framed `zkc.language.schema/0`, textual kind, nominal
`identity`, custody, constructible, Copy/Drop (each `0` or `1`), leaf count and ordered
leaf spellings, field count and ordered fields, then alternative count and ordered
alternatives. Counts and offsets use unsigned decimal text. A field contributes
its name, offset and child schema digest; an alternative contributes its name,
field count and fields. Display type spelling is excluded. This binds member names
and structure across captures even when nominal names and native leaves agree.
These identities retain names and printing policy; they are not semantic equivalence.
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
`path` and actual `role` name. Native slices are derived from the admitted logical
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
`boolean`, `index`, `field`, `group`, `unit`, `tuple`, `array`, `record`, `variant`,
`associated` and `builtin`. Scalars have their matching single native leaf; unit
has none. Tuples/arrays have positional fields, with one common element identity
for nonempty arrays. Records have identifier fields; associated representations
have exactly one `value` field. Only variants have alternatives. An empty product
cannot hide data leaves. Custody belongs only to nominal kinds.

`identity` is the lowercase SHA-256 digest of the closed canonical source type
key used by nominal custody and variant descriptors. It includes static arguments,
including phantom and zero-length array element types. The key encodes the type
kind tag, symbolic flag, length-framed domain and normalized dimension, then the
argument count and recursively framed argument keys; a natural uses its kind tag
and framed normalized dimension alone. Tags follow `Type::Kind`; framing is an
unsigned decimal byte length followed by `:` and the exact bytes. The toolchain
identity fixes this encoding. Native custody carries the exact digest; a variant
carries `["zkc.language", lowercase_hex(full_preimage)]`. The preimage is the
complete original UTF-8 type key. Both C++ and Rust readers require even-length
lowercase hex, check encoded expansion and decoded byte bounds before allocation,
validate UTF-8 and hash the decoded bytes. A chosen label or a digest in place of
the preimage refuses. The reader checks both anchors. Other source type identities
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
functions expose their Host plan instead. Host authentication must bind the retained
interface bytes, not arbitrary caller JSON that happens to compare semantically.
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
JSON nesting to 256 and lexical nodes to 200,000 before structural decoding.
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
The retained original uses standard `func` and `scf` control. Its `entry.stop`
operation never returns; typed SSA results close only the immediate unreachable
return/yield required by the enclosing region. The correspondence reader checks
that exact continuation. These results do not construct data or execution authority;
the executable Host stop has no results and bypasses the continuation.
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
