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
construction has only `kind: "authored"`; a derived construction has exactly
`kind: "fiat_shamir"`, `suite` and logical `service` index. Independent reading
checks these choices against the original signature and the exact native statement.
Source comparison separately checks that they match the selected checked Entry.

`setups` is an array of records with exactly `name` and `inputs`. Each input
selector has exactly `port` and `path`, using logical input and product-field
indices. Native slices are derived from the checked schema. Readers check exact
coverage, nonoverlap, nonempty selections and proof-key availability. Source
comparison additionally binds slot names and selector choices to the checked
Entry. Setup metadata is part of authenticated package bytes.

Each protocol record has `symbol`, `roles`, `inputs`, `outputs`, `services` and
`clauses`. Each port has `name`, display `type`, `roles`, logical `index`, ordered
native leaf indices in `native`, and recursive `schema`. A schema has `kind`,
`identity`, display `type`, `custody`, `permissions`, `leaves`, `fields` and
`alternatives`. Fields have `name`, leaf `offset` and child `schema`; alternatives
have `name` and payload `fields`. Zero-leaf ports retain empty native indices.
Offsets are relative to their product or alternative payload.

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
`identity`, custody, Copy/Drop/Share/Wire (each `0` or `1`), leaf count and ordered
leaf spellings, field count and ordered fields, then alternative count and ordered
alternatives. Counts and offsets use unsigned decimal text. A field contributes
its name, offset and child schema digest; an alternative contributes its name,
field count and fields. Display type spelling is excluded. This binds member names
and structure across captures even when nominal names and native leaves agree.
These identities retain names and printing policy; they are not semantic equivalence.
The formula helper name is `zkf_` followed by lowercase SHA-256 of the bytes
`zkc.language.predicate:` concatenated with the native declaration key. Its JSON
link must equal that derived name. Native formula admission requires a private,
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
no selectable element field is invented for it. Promised Copy, Drop and
Wire permissions cannot exceed native leaves; aggregate Share is checked through
logical children while native admission checks actual placement.

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
selects its Entry's protocol record. Host authentication must bind the retained
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
`assets`. Original MLIR, interface JSON and native run bundle or proof
deployment are exact strings. Options contain Boolean `simplify` and
`release_storage`. The job kind and complete source interface remain in the
retained interface, avoiding a second name or participant table. Package SHA-256
covers the exact emitted bytes, including source capture, selected Entry,
toolchain, compilation options and assets. Complete Entry aliases can share
executable bytes while naming different packages.

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
