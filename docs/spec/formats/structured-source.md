# Structured source export

`zkc-compile protocol-structured FILE --symbol=NAME` verifies the supplied
protocol-profile MLIR and exports a selected function with its retained
declarations. It performs no preparation, participant projection, finite
selection or realization. `original` names this export boundary; it does not
prove how an externally supplied module was produced.

Each `protocol.func` retains its own ordered participant roster and port scopes.
The complete unit is checked: supported unused
definitions are retained, and unsupported definitions are refused. Symbol names
are nonempty and unique across functions, domains, relations and operation
bindings. Helper references form an acyclic
graph; helpers cannot call protocols. Retained protocol applications form their
own kind of dependency edge in the same complete cycle/depth check. Selection
does not make a statement-free protocol uncallable from an acyclic sibling.
The independent
[formal admission contract](../../../lean/docs/spec/structured-source.md)
defines the Lean interpretation.

Ordinary source helpers use scoped `func.func`/CF bodies. Before exporting
their logical `local` meaning, the execution reader checks the complete actual
closure, scope ownership, outcome dispatch, failure propagation and transfer
cleanup. The exporter consumes that checked control association and the
original SSA operands. It does not infer a body from `runtime.origin`, strip
scope ports from an unchecked function, or rebuild a Local-dialect module.
Private outlined control bodies become closed formal regions. Distinct formal
arguments remain distinct even when their caller's actual arguments alias.
Invariant loop captures retained by the parent scope are explicitly forwarded
in the formal region's result tuple.

Supported `exec.compute` and ordered `exec.fold` occurrences retain their actual
mathematical helper or domain/callback references. Their logical signatures
become private `realize`, `finite` or `collect` declarations in the export; generated names
identify these declarations and supply no mathematical evidence. The source
hash still identifies the original, unexpanded MLIR. This checked export and
independent Lean admission are not a native execution correspondence theorem.

## Envelope and types

The current format is an exact tagged array, `zkc.structured-source/0`:

```text
[format, "original", source-sha256, entry-name, domains, relations, bindings, definitions, contracts,
 catalogue, source-declarations]
```

`source-sha256` is `sha256:` followed by 64 lowercase hexadecimal digits, hashing
the exact supplied MLIR bytes. It identifies those bytes; it is not a proof of
their semantics or of export correctness. Every record below has the exact
displayed arity. Unknown tags, extra fields and unrepresented native attributes
are refused.
All eleven slots are required, including empty tables. Each declaration category
preserves its native encounter order. Private computation declarations derived
from scoped bodies follow the native declarations in reader encounter order.
There is no cross-category declaration-order field.

| Type | Native interpretation |
|---|---|
| `["bool"]` | `i1` |
| `["index"]` | unsigned 64-bit index |
| `["field", domain]` | nominal scalar field |
| `["vector", domain]` | immutable vector over that field |
| `["group", domain]` | nominal group |
| `["groups", domain]` | immutable vector over that group |
| `["indices"]` | immutable ordered unsigned indices |
| `["oracle", kind]` | logical occurrence anchor, with associated Data/Query/Answer |
| `["oracle_sequence", kind, maximum]` | bounded ordered logical handles; `maximum` is a uint64 decimal string |
| `["service", contract]` | owner-local reusable service reference |
| `["sequence", element-type]` | ordered immutable `data.sequence` |
| `["product", identity, constructor, component-types]` | one-constructor packed product, with ordered components |

A product retains the complete canonical JSON encoding of its native nominal
descriptor, its single constructor label, and all flattened component types in
order. Equal shapes do not identify different products. This represented identity
does not replace the frontend schema that associates source fields with ports.
Types nest at most 64 levels; a product has at most 512 components. Every nested
domain is checked, including in dormant declarations. Nested service handles
and multi-constructor variants are outside this profile.

A domain is a native catalogue identity: field and vector types name a `Field`
identity admitted for that logical kind, group types a `Group` identity admitted
for `group`, and service types an installed random-service contract. The
`catalogue` slot carries the rows of every identity the export uses, closed
under associated members, in native catalogue order, and the rows of the
services it uses:

```text
catalogue := [nominal-rows, service-rows]
["nominal", identity, sort, [[member, identity]...], [capability...], modulus | null]
["service", contract, sampled-field, [method...]]
```

A nominal row is the native row: its sort (`Field`, `Group`, `Commitment` or
`Transcript`), its associated members, its capability facts in native order
and, for a field, its modulus as a canonical decimal string. A service row
names the field the service samples and its methods: `draw`, and `index`
exactly when that field has `IndexRandomness`. The exporter writes the rows of
whatever the native catalogue admits; an importer admits only identities whose
rows agree with its own catalogue (the
[formal admission contract](../../../lean/docs/spec/structured-source.md#domain-catalogue)
lists BLS12-381 and the supported KoalaBear base/extension rows and services).
Services originate at protocol
input roots and may be query handles or actual protocol application arguments.
The native
[service contract](../runtime/services.md) requires singleton ownership and
permits same-owner root aliases; services cannot be selected, restricted,
exchanged, returned, passed to Math/Local helpers, or bound as statement data.
Affine resources, multi-constructor variants, matrices, general arrays, arbitrary kernels and other
unlisted operations require a separately specified extension.

## Retained source declarations

The last slot is `[records, protocols]`, or `[[], []]` when no reachable source
protocol port contains a linear record. The frontend retains closed typed source
terms and field order before flattening:

```text
record := [closed-record-type, "ordinary" | "affine" | "linear", sealed, [[field-name, closed-type]...]]
protocol := [native-symbol, input-ports, output-ports]
port := [source-name, closed-type, [holder...], native-offset, native-count]
```

The terms use the existing typed origin grammar, including closed static
arguments. This is declaration context, not a new claim keyword or a routing
language. It is stored as canonical JSON in the original module's optional
`source_declarations` string attribute. Frontend correspondence recomputes that
attribute exactly from the checked closed source. A standalone MLIR export
cannot establish its frontend provenance. Projection removes this context
with the other original-only contracts; provenance uses the retained original.

The bounded Lean reader reconstructs Boolean/index/field/group, tuple, bounded
array, field-vector and recursively declared record layouts, then compares
exact native types, offsets and role scopes. It checks a single holder for each
linear source port. A protocol with any retained clauses must associate every
linear port with one relation, with consistent relation identity for repeated
uses of the same closed type. The relation comes from actual checked
subject/residual selectors. A clause-free protocol exposes resource boundaries
without asserting or inheriting a relation; its linear ownership must still
reach a consumer or residual on every successful exit. Records with native
resource markers, packed products, variants and unlisted carriers refuse rather
than being inferred from their flattened shapes. The selected protocol may have linear inputs or
residual outputs: selection fixes the library subject under study. It does not
declare a deployed proof Entry or discharge a residual relation. Concrete claim
selection must still check its fixed target and root acceptance interface.
Unknown and duplicate declaration rows, fields or owners refuse. There is one
current eleven-slot version-zero schema; a ten-slot envelope is not accepted.

## Declarations

```text
["domain", name, input-types, constructors, returned-domain]
constructor := ["elements", container-argument]
             | ["indices", container-argument, 0]
             | ["range", lower-argument, upper-argument]
             | ["zip", domain-references]
             | ["product", domain-references]

["function", name, kind, visibility, input-types, output-types,
 interface, preconditions, origin, body]

interface := ["protocol", role-names, input-scopes, output-scopes]  # protocol
           | []                                                  # math/local

["relation", name, visibility, kind, key, revision,
 static-arguments, input-types, output-types, purposes, formula]

["binding", name, contract, domain-arguments, implementation]

["finite", name, visibility, input-types, output-types,
 domain-name, step-name, predicate-name]
["collect", name, visibility, input-types, output-types,
 domain-name, body-name, predicate-name]

["realize", name, input-types, output-types, math-helper]
["map", name, input-types, output-types, math-helper, rowwise]
```

Domain data references select exact input arguments. Domain references use a
separate de Bruijn context: zero is the most recently constructed descriptor.
Each constructor binds one descriptor; `returned-domain` selects the actual
`data.domain_yield` operand after the complete sequence. At least one constructor
is required. Every stored constructor contributes to the instruction budget,
including unused ones, and a domain has at most 4096 constructors.

Elements and indices select field vectors or sequences and check u64 length
representability. Only axis zero is admitted. Ranges check both index bounds
before enumerating the half-open interval; reversed bounds yield an empty list.
Strict zip requires equal lengths and concatenates complete item tuples. Products
enumerate the last factor fastest. Both require at least one descriptor and
preserve argument order, duplicate factors and unused domain constructors.
Admission of the complete sequence precedes the first callback. Matrix domains
and other collection types remain outside this export profile.

Function `kind` is `protocol`, `math` or `local`; visibility is `public` or
`private`. Each protocol has 1 to 16 unique nonempty native role strings. Every
port has a nonempty scope drawn from that protocol's own roster; scope counts
match the signature. Owner references are local to that roster, including in
unused protocols. The writer retains native names without reconstructing
authored names or imposing the selected root's roster on other definitions.

Relations are non-callable metadata, retained even when unused. The declaration's
`kind`, `key` and `revision` are exact strings. `static-arguments` is a required
ordered list of the canonical typed terms used in protocol origins, including
unused static arguments. There is no ten-slot compatibility reader. The list
has at most 128 arguments, depth 64 and 4096 aggregate term nodes. Domain leaves
require matching exported and admitted catalogue rows even when no runtime
input mentions them. Native verification checks
their validity and consistency, the ordered signature, and each input purpose
(`parameter`, `statement`, or `witness`). A relation has one Boolean result.
`formula` is null or the exact symbol of a defined Math helper in this unit.
For `kind = "zkc.language.formula/0"` the link is required and its full ordered
input/output signature must equal the declaration's signature. Other kinds use
null. A Local function cannot satisfy a Math formula link. Names and hashes do
not infer this association; the original `relation.declare` owns it. Structural
association supplies no totality, relation adequacy or security proof.

Vendor kinds (outside `zkc.`) have identity `(kind, key, revision,
static-arguments)`. Equal identities require identical ordered logical types
and purposes; aliases may change formal names. Structural import retains this
identity without choosing a predicate. Registered meaning admission separately
requires the family's fixed typed instantiation to accept these exact arguments
and signature. Formula and captured kinds require empty static arguments and
keep their body/asset-owned interpretation.

The `contracts` table has exactly one row `[owner-protocol, clauses]` for every
exported protocol, including those with no clauses. Missing, repeated, unknown,
Math and Local owners are refused. Rows follow native protocol encounter order;
clauses retain declaration order, independently of the selected entry.
Each owner has at most 512 clauses, and each application at most 512 selectors,
matching the structured profile's signature bound.

```text
clause      := [kind, name, subject, residual, decision]
application := [relation-symbol, [selectors...]]
selector    := [direction, native-port-index, role]
```

Kind is `target`, `input`, `output` or `continuation`; names are nonempty,
unique per owner and at most 512 UTF-8 bytes. Spaces, dots and Unicode are
permitted in hand-authored clause names. Direction is `input` or `output`. Each selector names an
actual port and an available role of that owner. An application has exactly
one selector per native relation input, in ABI order, with exactly matching
types. Input and continuation subjects select only inputs; output subjects
select at least one output. Targets may describe either boundary, but an entry
statement can project only a target over inputs. A continuation requires a
residual application selecting at least one output; all other residuals are
null. A decision is null or exactly one available Boolean output selector.
Targets require decisions, input clauses forbid them, and output/continuation
clauses may carry them. Unknown tags, extra fields and malformed nulls refuse.

Contracts are declaration metadata, not instructions or predicate evaluations.
An entry statement may name its exact selected target. That name resolves only
within the statement's owning protocol, and its relation, input arguments,
input roles and acceptance index must agree with that target. The selected
clause supplies the exact decision role. A dormant protocol's matching clause
cannot satisfy the reference, and a dormant statement does not select the
export root's target. Without a target name, standalone statements are permitted;
if their owner has targets, their projection must match at least one. Such an
unnamed statement supplies no exact selected-target evidence. Component
application does not turn contracts into entry statements. Its actual body and
role substitution determine invocation bindings.

Operation bindings are non-callable metadata for `runtime.binding`, retained and
checked even when unused. The exact represented native attributes are
`sym_name`, `contract`, `arguments`, and `implementation`; no signature, body,
visibility, or execution parameters are invented for them. Names match ASCII
`[A-Za-z_][A-Za-z0-9_.-]*` and have at most 256 bytes. Index contracts require
empty domain arguments; vector and field contracts require exactly one
`Field` identity, whose row the catalogue slot carries. The implementation selector must be the explicit empty
string. Selected implementations and contracts outside the catalogue below are
refused, including on dormant declarations. Distinct binding names with the
same metadata remain distinct retained rows.

### Definition origins

Math preconditions are exact arrays
`["index_bound", index-argument, container-argument, 0]`. Other relation
annotations are refused. Math origin is `[]`; Local origin is
`[origin-name, [[key, value], ...]]`, preserving the ordered `logical_origin`
bindings without flattening them or substituting the helper symbol.
Bindings have unique nonempty keys and nonempty values, with at most 128 pairs.
The native verifier validates binding values against installed and canonical
static identities. Lean retains these values as opaque metadata and checks their
shape and uniqueness; it does not independently reproduce that identity registry.
Protocol origin is required in this export and is carried by the native `origin`
attribute. It uses a public typed tree, independent of generated symbols,
internal type identities, display spellings and physical layouts:

```text
origin := [template-path, [[parameter-name, term], ...]]
term   := ["nat", decimal] | ["field", id] | ["group", id]
        | ["domain", sort, id] | ["asset", sort, id]
        | ["bool"] | ["index"] | ["unit"]
        | ["tuple", [term...]] | ["array", term, decimal]
        | ["nominal", "record"|"variant"|"associated"|"module", path, [term...]]
        | ["builtin"|"formal", name, [term...]]
```

The template path is the logical qualified NFC declaration path, without a
filesystem path, capped at 2048 UTF-8 bytes. Named arguments occur in declaration
order with distinct names; a nongeneric declaration has an empty argument list.
Other strings have at most 512 bytes. Decimal strings are canonical unsigned
base ten. Each origin permits at most 128 named arguments, 4096 term nodes in
total and 64 term levels (the root term counts as one). Recursive term lists
permit at most 512 entries and preserve order. The native input's separate
textual nesting and byte limits also apply. Symbolic terms and unbound parameters are refused; a closed
`formal` constructor is permitted. These trees identify a proposed callee;
source comparison separately checks the checked declaration and body. An origin
alone establishes neither body equality nor native/formal correspondence.
Handwritten native IR may omit this source metadata, but cannot then be exported
by this profile; no origin is inferred from its symbol. Local and protocol
origins are decoded by definition kind and do not share a binding-value grammar.

Math helpers are private.
Native protocol formation currently permits no explicit `sym_visibility`
attribute, including an explicit `public`; its retained visibility is the
default `public`. The general function record does not override that formation
restriction or impose the Math helper's private-only rule on protocol calls.

A finite declaration records an admitted `exec.fold` occurrence, and a collect
declaration records `exec.collect`. Their keys are private export-local identities
associated with actual occurrences, not native declarations inferred from names.
The empty predicate name means no predicate. The [finite ABI](../ir/finite.md)
retains `A ++ S ++ C` for folds and `A ++ C` for collections. The step receives
`S ++ I ++ A ++ C`; a collection body and predicate receive `I ++ A ++ C`.
`I` is the complete ordered tuple of domain items. Callbacks are actual private
scoped functions whose admitted CFG is exported through its data arguments and
successful outcome payload. A collection returns one field vector or sequence;
its body returns that collection's single element type. False predicates skip
an item. Predicate and body stops retain the first reached stopping reason.

A realization record associates an actual `exec.compute` occurrence with its
exact private Math helper and full data ABI. Native frontend maps export their
actual collect, domain and scoped callback. Their scalar-map equations are proof
obligations over those bodies, not an export classification inferred from a
generated name. Every declaration and callback is checked, including dormant
ones. The independent formal vocabulary also admits the `map` record below;
the native exporter does not produce that constructor or a separate map callable.

A realization has exactly the helper's full ordered input/output ABI, including
unused inputs and zero or multiple results. Its derived Local meaning is one
ordinary invocation of that helper. The original declaration remains distinct
from the derived body. The transitive Math computation may contain admitted pure
field/group/Boolean/index operations, selection, nominal product operations,
Math calls, finite folds, checked reads and returns. The root has no external
preconditions. Ordinary formation discharges internal call and callback bounds,
including dead calls; both fold callbacks belong to structural admission even
for empty domains. Admission does not establish unconditional return: reached
finite domains retain their length check and possible exhaustion. The Lean
immediate-return theorem uses a separate narrower checked fragment.

A map root takes scalars of one field identity and returns exactly one such scalar.
`rowwise` is a Boolean array with exactly one entry per input and at least one
true. A true position lifts that scalar to a vector; a false position remains a
scalar broadcast. The result is one vector. Every transitive instruction,
including dead calls and unused results, must belong to that field's ring
fragment: constants, add, subtract, multiply, Math calls and return. Nested
callees may return zero or multiple scalars; the one-result restriction applies
only to the root. All helper preconditions are empty. Equality, selection,
indices, groups, finite operations and other fields are outside this map profile.

Both native tools run native formation before their separate structured checks.
Native formation checks the complete actual scoped closure and mathematical
bodies, including dormant definitions. The independent C++ observer's Fr-only
restriction and structural capacity limits remain independently observable.
Native formation accepts a wider realization fragment than the conservative
structured closure above. Formal map records have their own checked ring
fragment; their admission is not evidence about a native source map.

Preparation records are export-local associations with actual `exec.compute`,
`exec.fold` or `exec.collect` occurrences in scoped functions. Ordinary
`func.call` composes those functions; `protocol.local_call` enters an actual
scoped function from protocol control. Math calls cannot invoke ordered
preparations. Finite callbacks remain actual private scoped definitions with the
borrowed scope and outcome ABI, not derived callable declarations.

## Blocks, binding and control

```text
["block", instructions, terminator]
[descriptor, operand-indices, result-types, regions, site]
[input-types, output-types, body]                     # region

["return", indices]
["yield", indices]
["condition", indices]                              # Boolean first
["stop", reason, site]
```

A block starts with its inputs in original order. Each instruction prepends
its full ordered result list to the current context. Older references shift by
that list's length. Zero-result instructions leave the context unchanged but
still execute. Return and yield references preserve order, repetition and
identity even when their types coincide.

Regions are closed: their arguments are the actual explicit captures and loop
state, with no implicit access to the surrounding context. An `if` has two
regions from captures to result types. A `for` body takes
`index :: (state ++ captures)` and yields `state ++ captures`; a conditional
body yields a leading Boolean followed by state and captures. Continuing
captures must be the identical input values, accounting for the prefix of body
results. Type equality alone does not establish forwarding.
An unconditional stop in a loop body uses `for`; `for_condition` requires a
condition terminator. Nested branches in either form may still stop.

Pure mathematical instructions have empty sites. Local call/control instructions retain
their actual required sites, as do exchanges, draws and guards. Restrictions and
statements have empty sites. Nonempty sites are unique within a definition,
including nested regions. Stop reasons are `reject`, `abort`, `exhausted`,
`incomplete` and `refused`.

## Descriptors

| Descriptor | Meaning and interface |
|---|---|
| `["index.constant", decimal-string]` | pure canonical u64 constant |
| `["index.equal"]` | pure two-index equality to Boolean |
| `["exec", "exec.apply", binding-name, parameters]` | checked Local primitive occurrence from the catalogue below |
| `["field.constant", domain, literal-string]` | canonical scalar constant: a decimal residue, or for a binary field a [bit-pattern literal](../domains/values.md#bit-pattern-literals) |
| `["field.add" / "field.subtract" / "field.multiply", domain]` | two fields to one field |
| `["field.equal", domain]` | two fields to Boolean |
| `["field.embed", extension, base]` | one base-field value to the named extension field |
| `["group.identity", group]` | group identity |
| `["group.add", group]` | two groups to group |
| `["group.scale", group, field]` | group then associated scalar field to group |
| `["group.equal", group]` | two groups to Boolean |
| `["bool.constant", value]` | Boolean constant |
| `["bool.and" / "bool.or" / "bool.xor" / "bool.equal" / "bool.not_equal"]` | two Booleans to Boolean |
| `["select", type]` | Boolean and two equal-typed values to that type |
| `["bounded_at", domain]` | vector and index to field, with exact bound obligation |
| `["product.make", constructor]` | ordered components to the exact declared product |
| `["product.get", index]` | total projection of a component at its checked type |
| `["call", name]` | ordinary Math helper call |
| `["apply", name]` | Local function, finite, collect, realization or map declaration call |
| `["local_call", name, participant]` | Protocol call to an actual Local function with exact owner |
| `["protocol_apply", name, role-names]` | Retained static protocol application with positional role substitution |
| `["protocol_repeat", carried, maximum, roles, carried_roles]` | Retained protocol repetition with one isolated optional-state callback |
| `["fold", domain, step, predicate]` | ordered finite Math fold |
| `["if"]` | Local conditional over closed captures |
| `["for"]` / `["for_condition"]` | Local counted control |
| `["guard", participant]` | Protocol guard with exact owner; false rejects |
| `["restrict", role-names]` | same value restricted to the retained scope |
| `["exchange", sender, receiver]` | sender alias and independent receiver value |
| `["draw", owner, field]` | query the actual service handle operand; one field result |
| `["statement", relation, selectors, acceptance-index, target]` | ordered entry operands; zero results; target is a clause-name string or null |

Every operand, result and region interface is checked against the selected
descriptor and referenced declaration. A same-typed result permutation can be
a valid different program. It is preserved rather than classified as a type
error. A bound for a different same-typed vector does not authorize a read.

A statement's selectors are actual native role strings, one per operand. Native
verification checks that each operand is an entry argument available at its
selector, with the exact relation input signature. The acceptance index selects
a Boolean result of the enclosing protocol; zero and nonzero indices are
preserved. All five descriptor fields are mandatory; there is no four-field
compatibility form. Source proof selection retains the exact target name,
distinguishing targets that share the same operand and output indices but select
different role-local decisions. This does not prove complete source Entry or
provider correspondence. A statement does not evaluate a relation, assert
satisfaction, or identify different participants' copies of an acceptance result.

Ownership is checked independently of operand types:

| Body kind | Admitted instructions |
|---|---|
| Protocol | Pure index constant/equality and field/group/Boolean operations, select, product construction/projection, Math call, Algebra fold, Local call, protocol application and repetition, guard, restrict, exchange, draw, entry statement |
| Math | Pure index constant/equality and field/group/Boolean operations, select, product construction/projection, bounded read, Math call, Algebra fold |
| Local | Boolean constant, checked primitive execution, Local apply, conditional and counted control |

The descriptor can represent selection of any admitted value type. The current
native mathematical verifier admits Boolean, scalar-field and group selection in this
profile; vector and index selection are not yet native export paths.

Only Local bodies may end in an explicit stop. A guard retains the owner of
the original `protocol.guard`; projected participant guards are outside this source
stage. Conditional entry completion and construction-start
selection remain outside this profile, including dormant definitions.

Multi-role protocols cannot use Math folds or bounded reads, including through
retained Math helpers. Those combinations require additional partial-component
semantics. Existing single-role finite programs and owned Local finite work
remain supported. Math calls propagate each input's availability through the
actual helper body: `first(x,y) = x` does not require `y` at the same participant.
Native verification also checks availability of unused intermediate expressions.
Local calls require all inputs at their owner, execute there even with zero
results, and do not execute at other participants. Restriction and declared
output scopes never erase preceding effects or stops.

## Logical oracle vocabulary

These rows describe the original oracle-level subject, before semantic
realization. The native exporter checks the common protocol formation rules,
including dormant declarations. The independent Lean wire reader recognizes
these rows. Lean semantic admission currently refuses logical oracle execution; decoding does not extend its existing participant theorems.
Component seam derivation also refuses logical oracle instructions when linear
component analysis is active. An empty proposal set asserts no oracle seam.
Frontend syntax, generated obligations and deterministic realization remain
separate implementation work; see [status](../../status.md).

Kinds retain the library identity and typed arguments:

```text
kind := ["table", [["type", row-type]]]
      | ["table", [["type", row-type], ["nat", rows]]]
```

`rows` and sequence capacities are canonical decimal strings in `0..2^64-1`,
including zero. They are logical cardinalities, independent of execution work
limits. Associated types are derived: Query is `index`, Answer is `row-type`,
and Data is `vector` for field rows, `groups` for group rows, `indices` for
index rows, or `sequence(row-type)` otherwise. The kind does not select a
commitment scheme, leaf layout, native handle or codec. Nested services or
logical handles cannot become ordinary row data.

Every instruction uses the existing five fields:
`[descriptor, operand-indices, result-types, regions, site]`. All oracle
instructions have an empty `regions` array. Operand indices use the existing
prepend-results convention. The kind in a descriptor must agree with the
actual operand/result types; retaining it does not authorize a different kind.

| Descriptor | Ordered operands | Results | Site |
| --- | --- | --- | --- |
| `["oracle_input", holder, receivers, kind, maximum-or-null]` | holder data, receiver anchor | role-family handle | empty |
| `["oracle_send", holder, receivers, kind, maximum-or-null]` | data, rows | handle | send occurrence |
| `["oracle_query", owner-or-null, kind]` | handle, position | answer | query occurrence or declaration-local label |
| `["oracle_contents", holder, kind]` | handle | data | empty |
| `["oracle_components", holder, receivers, kind]` | handle | holder data, receiver anchor | empty |
| `["oracle_rows", kind]` | handle | index | empty |
| `["oracle_forget_rows", sized-kind, unsized-kind]` | sized handle | unsized view of the same anchor | empty |
| `["oracle_virtual", declaration, holder, receivers, kind]` | source handles, ordinary parameters | fresh virtual handle | empty |
| `["oracle_sequence_empty", kind, maximum]` | none | sequence | empty |
| `["oracle_sequence_append", kind, maximum, roles]` | sequence, handle | sequence | bounds-check occurrence |
| `["oracle_sequence_at", kind, maximum, roles]` | sequence, position | selected handle | bounds-check occurrence |
| `["oracle_sequence_length", kind, maximum]` | sequence | index | empty |

An owner is absent only for a query inside a virtual declaration. Send and
query sites remain ordered events, including repeated or unused queries.
Sequence append/selection retain their stopping checks. A virtual construction
has an occurrence identity from its structural row and actual invocation/loop
coordinates, without inventing a query event or using a diagnostic location as
identity. Shape and capacity are distinct: an unsized anchor has an immutable
row count; a sequence has a maximum number of handles.

Virtual declarations occupy the existing `definitions` table:

```text
["oracle", name, input-types, kind, admissibility-relation,
 shape-argument-or-null, maximum-rows-or-null, block]
```

Source handles form the input prefix, ordinary parameters follow, and the
queried position is last. The block returns one value of the kind's Answer
type. Its query labels are local to that declaration, and its actual source
operands and mathematical helper bodies determine the ordered footprint.
Shape argument and maximum are decimal strings and occur together only for an
unsized kind. The shape argument selects an ordinary parameter, not the queried
position. The native checker verifies the actual admissibility relation over
source Data values and ordinary parameters, without proving it. A same-named
replacement declaration is not correspondence evidence.

An input binding exposes exactly two interface leaves, data at the holder and
an anchor at receivers. Shape belongs to that anchor; there is no third shape
leaf or duplicate source port. The generated honest-input relation must connect
those two leaves without appending or renumbering authored contract clauses.
A call rebinds its actual anchor; it does not allocate another root input.
`oracle_contents` is executable only at an admitted holder. A future
relation-side anchor selector has separate permissions and supplies no
verifier-side data extraction operation.

The original snapshot and its row associations remain intact when a later
construction selects a realization. That realization must produce ordinary
protocol operations before participant projection; unresolved logical oracle
operations cannot be serialized as physical handles in the
[program byte language](program-bytes.md). The original and the deterministic
realization record are the independent checker's inputs. Recognizing the source
or output grammar proves neither realization correspondence nor commitment
security.

## Retained protocol application

The exact native attributes of `protocol.apply` are `callee`, `roles` and `site`.
The existing instruction row carries its full ordered operands and results, no
regions, and its nonempty authored site. The descriptor does not duplicate the
site. The target is a defined protocol in the same unit; `role-names[i]` maps
its ith local role into the caller roster. The mapping is total and injective
and may use a proper subset of the caller's roles. The complete ordered ABI and
all required input availability are checked, including unused inputs. Service
ports retain their exact contracts, mapped singleton owners and lexical input
origins. Applications cannot target components containing entry statements.
All references and bodies are checked even when unused or unreachable from the
selected root. Ordinary Math/Local and preparation call rules remain unchanged.

The independent SSA reference passes an immutable protocol context: a mapping
from callee-local roles to root participants and an optional accumulated static
application prefix. Root self never changes. At a call, role mappings compose
positionally. The child prefix is the current application site's already
qualified spelling. With `p(a,s) = "apply_" ++ decimal(UTF8Bytes(a)) ++ "_" ++ a
++ "_" ++ s`, nested A/B/C renders `p(p(A,B),C)`. Qualifying at the root is
identity; qualifying the empty synthetic site always yields the empty string.
Native authored sites themselves are nonempty identifiers.

A participant outside the mapped callee roster skips the body and returns an
absent tuple of the exact output arity, including zero. Participating calls mask
optional inputs to the callee interface, evaluate the original body, and mask
successful outputs. Entry does not strictly demand every optional argument.
Owned Local calls still demand all arguments, even unused inputs, and a missing
argument stops at the qualified protocol call site. A reached Local helper stop
retains its raw helper-local site. Math and Local helper bodies have their own
unqualified observations. One SSA evaluation core owns all these operations;
no production expansion or generated execution IR supplies the meaning.

Guard owners, restriction membership, action owners/peers and protocol sites
use the context. Received values and service handles remain the actual values;
same-owner aliases preserve one handle and ordered state use. Zero-result calls
still perform effects and propagate the first stop before the caller continues.
The existing request/reply records and consumption rules are unchanged.

Original nonempty site uniqueness includes application headers. An additional
read-only traversal checks effective expanded-site uniqueness for every original
protocol root, including unused roots. It revisits each application occurrence,
advances its prefix, and excludes the erased call header from the effective set.
All ordered protocol categories and owners share one set per root. Protocol Local
call sites are included; helper-internal sites belong to separate namespaces.
No reserved `apply_` prefix rule is imposed. A generated collision is refused
before export or reference execution, without materializing expanded syntax.

This traversal counts every static operation, including site-free work and
terminators, and bounds total visits over all roots to 100000. Application stack
depth includes the root and is at most 64. Each rendered label is at most 4096
UTF-8 bytes; cumulative rendered label work is at most 16 MiB, including erased
headers. Lengths are checked before concatenation. These limits are separate
from the 512-byte stored source-string bound and the observer's execution fuel.

Native formation additionally enforces the conservative application/Math
expansion summaries specified by [composition](../ir/composition.md): boundary
restrictions, pure helper work, return/header overhead, SSA/role slots, and
intermediate site lengths all count. A smaller effective-site set cannot replace
those preflight checks. The native reference and exporter independently check
effective collisions after native formation; the independent formal reader must
establish its own budget and effective-site obligations before claiming agreement
with this admitted native profile. No observer record format is added.

## Retained protocol repetition

The exact attributes of `protocol.repeat` are `site`, `carried`, `maximum`,
`roles` and `carried_roles`. The descriptor stores the latter four in that order;
the required nonempty site stays in the instruction row. `carried` and `maximum`
are JSON numbers. Native formation requires a nonnegative carried count equal
to the result count, smaller than the operand count, and a maximum in
0..1048576. The operands are `(count, state, captures)` with an unsigned-64 count.
Results have exactly the initial state types. There is one isolated callback:

```text
[index :: state-types ++ capture-types, state-types,
 ["block", instructions, ["yield", state-references]]]
```

Callback argument zero is induction, distinct from the outer count. An authored
use of that count requires an explicit capture. Only `protocol.yield` terminates
this callback; it yields state alone. Every callback is checked, even at maximum
zero, after a stopping instruction or in a dormant definition. Free outer SSA
references, nested statements and wrong callback interfaces are refused.
Native structural and scope errors diagnose `mathematical-formation` before
export or reference admission; parser/MLIR invariant failures can precede it.
Extra repeat/body attributes are refused by native `mathematical-formation`
before the structured whitelists. A nested statement or return fails the MLIR
parent invariant first, reported as `structured-source-original` or independent
`structured-reference-source`.
These wrapper identifiers alone do not identify which verification layer
refused. Native controls also check the actual invariant message in both tools.
A scoped execution stop inside a common repeat callback reaches
`mathematical-formation`; common callbacks admit protocol actions and must
yield the carried interface.

The repeat roster is a nonempty subset of the enclosing active roster. Count
availability covers it. Every state scope is nonempty, contained in that roster,
and available both initially and at yield. Capture availability intersects the
roster nontrivially. Nested applications, repeats and action owners cannot widen
it. Services are immutable captures, never state or results. Their lexical
origins follow the exact capture operands through nested callbacks to the
containing protocol's original service ports. Data captures do not become entry
ports; a statement cannot bind them. A copyable capture may replace a state
value at yield when its type and scope meet that slot's requirements.

The independent SSA reference retains the current role context and application
prefix. Outside the mapped repeat roster it returns an absent result tuple,
without inspecting count or captures, even when a present count exceeds maximum.
Inside, missing count stops `incomplete` at the qualified header; a count above
maximum stops `refused`. Wire inputs outside u64 are decoder errors, not a reached
overflow stop. Otherwise execution
starts with masked initial state and calls the original callback at indices
0 through count-1, passing that state and the unchanged captures. Every
successful yield is masked to `carried_roles`. Zero returns masked initial state
without invoking the callback. Optional state/captures are demanded only by
reached strict operations. Zero-state repeats still perform their body effects.
Stops preserve prior reply consumption and suppress later iterations and the
outer suffix. Actual service handles and shared provider state are not reset.

Each role uses its own count and received values. The native joint driver's
separate count-agreement check is not part of this per-role reference meaning.
The native Runner's source-bound failure is `loop-count-bound`; its resource
failures and the reference's `structured-reference-capacity` remain separate.
Earlier ordered actions remain before a zero repeat. Comparing eager pure
capture calculations with demand-driven native projection still requires the
existing totality and observation premises.

Repeat contributes no application prefix or iteration suffix. Its header and
body sites share the definition's stored namespace and the root's effective
namespace. Static traversal visits each body once per application occurrence,
including at maximum zero, and retains the header. It charges all body operations
and terminators against the existing 100000 visits, 4096 label bytes and 16 MiB
label-work bounds. Effective repeat depth is at most 64 and is carried through
application edges; violations diagnose `structured-source-limit` or independent
`structured-reference-capacity`. The native expansion re-verification enforces
its own `mathematical-formation` depth and collision obligations. Ordinary lexical JSON
depth 64 is a distinct wire-profile bound, not permission for 64 stored nested
callbacks. Reference-graph depth, application summary depth and observer depth
retain their existing definitions.

Complete unchanged repeat and nested-repeat sources, an ordinary service-order
wrapper, and the complete original Reduction/Sumcheck units can be exported and
admitted. Their native reference observations are bounded evidence. Full
Sumcheck symbolic equations, affine resource models and production correspondence
are separate obligations; no protocol-specific intrinsic supplies their meaning.

## Primitive execution

An `exec` descriptor retains the actual `exec.apply` operation, its binding
name and the exact ordered array of string parameters. It has zero regions and
a required nonempty site, unique within its logical Local definition. The
binding's contract selects the primitive. Each use checks nominal domain
arguments, full ordered data operand and successful payload types, parameters,
and Local ownership. Native scope/outcome ports belong to the admitted CFG;
they are not logical value ports in this descriptor. Binding names confer no
semantics by themselves. The exporter reuses the native logical catalogue for
these ABI checks; Lean independently admits this closed table. There is no
reader for retired per-primitive MLIR operation names.

Here `I` is index, `B` Boolean, `F` the binding's nominal field, and `V` an
ordered vector over that field. Every row uses the same `exec.apply` operation.

| Binding contract | Inputs → outputs | Parameters |
|---|---|---|
| `index.constant` | `[] → [I]` | `[n]` |
| `index.add` | `[I,I] → [I]` | `[]` |
| `index.sub` | `[I,I] → [I]` | `[]` |
| `index.mul` | `[I,I] → [I]` | `[]` |
| `index.div` | `[I,I] → [I]` | `[]` |
| `index.mod` | `[I,I] → [I]` | `[]` |
| `index.equal` | `[I,I] → [B]` | `[]` |
| `index.less` | `[I,I] → [B]` | `[]` |
| `vector.empty` | `[] → [V]` | `[]` |
| `vector.length` | `[V] → [I]` | `[]` |
| `vector.sum` | `[V] → [F]` | `[]` |
| `vector.split` | `[V] → [V,V]` | `[]` |
| `vector.append` | `[V,F] → [V]` | `[]` |
| `vector.equal` | `[V,V] → [B]` | `[]` |
| `field.equal` | `[F,F] → [B]` | `[]` |
| `field.embed` | `[field:base] → [field:extension]` | `[]` |

The `field.embed` binding takes one domain argument, the extension. Its
`BaseField` member fixes the operand's domain. The existing `exec` descriptor
retains this binding and its site; Lean lowers it to the same nominal embedding
operation as the direct descriptor. Embedding admission requires `ExtensionField`
and `Field` on the extension, `Field` on the base, an exact `BaseField` member,
and equal, present characteristic moduli. These checks select a domain pair;
they do not establish the algebraic laws of its interpretation.

`n` matches `0|[1-9][0-9]*` and denotes a value at most
`18446744073709551615`. Index inputs/results have the same u64 range, independent
of observer loop limits. Add/multiply overflow, subtract underflow, and zero
divisors for division/remainder stop `refused` at the primitive site. Comparisons
use unsigned order and equality; division/remainder use Euclidean integer laws.

Empty produces `[]`. Sum folds field addition from zero, including on an empty
vector. Length counts elements; a logical length outside u64 stops `exhausted`.
Split refuses empty or odd vectors, otherwise returning the contiguous first
half followed by the second half. Positive even length is sufficient, without
a power-of-two requirement. Both results enter SSA in that order. Append adds
one scalar at the end, retaining order and duplicates. Vector equality compares
length and ordered elements; unequal lengths return false. Field equality
compares canonical scalar values. Allocation/work limits are separate from
these logical laws.

Exec sequences all operands strictly and runs even when its results are unused.
An owned Local call with absent required inputs stops `incomplete`; nonowners
skip it. Pure `data.index` and `data.index_equal` export as the separate pure
descriptors with empty sites and no bindings. Pure index equality propagates
absent components. Pure scalar equality likewise remains distinct from Local
`exec.apply` with a `field.equal` binding.

Ordinary source wrappers capture the unchanged `multilinear::has_shape`,
`table`, and `halves` helper closures, including the private rows loop and
short-circuit guards. `table` checks shape; `halves` itself checks positive
dimension and split length, so its stronger shape interpretation requires the
constructor premise. An independent append/count example covers vector and
integer operations. The complete frontend original is exported without slicing
or preparation; unsupported dormant native declarations still refuse.

## Map and realization execution

The independent reference executes actual Func/CF bodies, including block
arguments, backedges, outcome dispatch, scoped calls and transfers. `exec.compute`
invokes the exact Math helper through that same independent SSA evaluator. It
passes every data argument and returns every result in order. It uses neither
the structured exporter nor production preparation or runtime kernels.
`protocol.local_call` sequences owned inputs before entering the scoped helper,
including unused projection inputs and zero-result invocations. Nonowners skip
the owned call.

Finite requests execute every stored domain constructor in order, including
unused results, before any callback. Strict zip concatenates complete tuples;
Cartesian product varies the last factor fastest. Each fold or collection
invokes its actual predicate before its body, preserving the first stop and
the original argument positions. Domain admission failure uses the finite
invocation site. A stop inside a callback retains that callback's site.

Map first measures the first row length, stopping `exhausted` if it is not below
2^64. It then visits each remaining row input in argument order, measures and
checks representability, and stops `refused` at the first unequal length.
All rows are checked, even when unused by the formula or when the first is empty.
An earlier mismatch precedes a later unrepresentable length. After that prefix,
rows are evaluated in increasing order with the complete scalar tuple in original
argument order, selecting each row element or scalar broadcast. Equal empty rows
return the empty vector without invoking the helper. Admission has nevertheless
already checked the entire unit and every helper body.

Frontend maps use `exec.collect` with ordered domain admission and a scoped
callback. Shape refusal uses that collection's invocation site. Discarding its
result cannot discard the stop or permit a subsequent interaction. The callback
passes the complete ordered tuple and broadcasts to its actual computation.
The independent observer checks the source outcome; relating selected native
failure codes, generated sites and resource effects requires a separate bridge.

Ordinary wrappers capture unchanged `multilinear::fix_first` and `fix_prefix`,
including their table constructor and values/variables/width projections.
`fix_prefix` uses scoped finite folds. An independently authored Fr linear
combination covers ordered broadcasts and unused scalar/row arguments. The native
library's KoalaBear Ext8 Combination remains outside this Fr-only profile.

Structured admission checks retained SSA, without production formula expansion.
Collections admit actual effectful callbacks; a specialized scalar-ring
optimization must separately establish eligibility of the selected computation.
Neither a generated name nor collection admission establishes that eligibility.

## Limits and evidence

The independent native SSA test executable retains its closed invocation:
`zkc-structured_reference-test FILE SYMBOL INPUTS_JSON`. Its single-role scalar
and finite inputs and outputs are unchanged.

Its scope and transfer identities check the observer's logical control and
custody, including one-time transfer consumption. They do not model backend
allocation, frame admission, cleanup failures or the native resource ledger.
Observer work, tuple-storage and vector bounds produce diagnostics, never
fabricated source stops. Native and formal agreement is bounded evidence, not
a theorem of CFG lowering or resource correspondence.

Open executions use a distinct command and exact request:

```text
zkc-structured_reference-test open FILE SYMBOL REQUEST_JSON
["zkc.structured-open-request/0", role, inputs, replies, step-capacity]

request := ["send", site, sender, receiver, type, value]
         | ["receive", site, sender, receiver, type]
         | ["draw", site, owner, contract, handle, field]
reply := ["reply", exact-request, response]
response := ["unit"] | ["value", value] | ["stop", reason]

["zkc.structured-open-result/0", outcome, records, reply-position]
outcome := ["returned", optional-outputs] | ["stopped", reason, site]
record := ["request", reply-position, request]
        | ["reply", reply-position, response]
        | ["stop", reason, site, reply-position]
```

Inputs occupy the original ordered ports; `null` is an absent component. The
selected participant's input scopes mask inputs, and output scopes filter results
after execution. Boolean values are JSON Booleans; field, group, index and service
values are canonical decimal strings; vectors are arrays of field strings.
Field and group test values use the existing BLS scalar modulus
`52435875175126190479447740508185965837690552500527637822603658699938581184513`.
The group is explicitly the additive test model over that modulus, not native
BLS points. Service handles are concrete natural numbers bounded to u64. Equal
handles at supplied roots must have the same owner; same-owner aliases remain
equal and are queried in order. These integers do not authenticate native roots.

Send expects a unit reply and retains the sent component locally. Receive and
draw expect a typed value. Missing replies stop `incomplete`; mismatched requests
or responses stop `refused` without consuming that reply. Valid scripted stops
consume their reply. Records retain exact requests, accepted replies and stops.
Positions are zero based; the final position counts consumed replies. Unused
suffix replies remain unconsumed. Every reply row must have the three-field
`reply` envelope with array-valued request and response; action equality and
response typing are checked when the reply is reached. Native Local stops and
failed owner guards retain their sites. Nonowners skip those operations.

The reference interprets original native SSA and retained helper bodies using
one evaluation core, without the structured exporter or serialized coordinates.
Math operands remain optional through calls; pure operations propagate absence,
while Local exec sequences operands strictly. Its eager Math execution needs a totality premise before
comparison with native demand-driven projection for potentially failing Math.
Native verification remains authoritative for formation. The reference bounds
step capacity to 1..1000000, replies to 4096, request and replay-record bytes to 1 MiB, vector
length to 4096 and loop bounds to 2^20; evaluation depth is 64, starting the entry
invocation at 1 and increasing for helper calls and nested execution regions.
This runtime observer bound is separate from reference-graph admission below:
an admitted 64-edge path can require evaluation depth 65 if fully traversed.
An empty map does not invoke its scalar helper, and nonowners skip owned Local
calls, so admission of that path need not exhaust evaluation capacity.
Capacity failures
are explicit `structured-reference-capacity` diagnostics, not simulated native
stops. This is bounded test evidence, not an interpreter correctness theorem.
Vector result lengths are checked before allocation. Sum, split and equal-length
equality charge one additional work unit per element; append charges its output
length. Length itself is constant work. An input/reply longer than 4096, an
append exceeding that bound, or insufficient observer work produces a capacity
diagnostic. A malformed typed reply instead stops refused without consuming it.
Map charges one unit per input position for its shape prefix, its output length,
the complete tuple arity per row, and existing helper invocation/instruction work.
Aggregate tuple work is fuel, not a vector-length bound: arity times row count
may exceed 4096. Charges are checked before construction/allocation without an
unchecked product. Shape comparisons precede output construction, although
ingress or observer capacity can prevent observing a semantic outcome.
The observer's finite vector bound makes the logical unrepresentable-length
exhaustion branch unreachable; it does not replace it with source refusal.

The writer bounds source bytes to 16 MiB, the complete exported file (including
its final newline) to 1 MiB, strings
to 512 UTF-8 bytes (protocol template paths to 2048 bytes, binding names to 256 ASCII bytes), domains, relations,
bindings and definitions to 128 each, signatures to 512
positions and total instructions to 4096. Operand references index the lexical
value list and are also at most 4096. The instruction count includes nested
bodies, domain constructors and one derived instruction per finite, realization,
collection or map declaration; it excludes terminators. The independent native
reference has a separate 4096-operation admission budget over actual native
nonterminators, including outcome packaging, and all domain-body operations. It
counts actual native definitions rather than export-local derived rows. Neither tool expands calls
for these counts. Both capacities are independent of runtime fuel; equality of
their numeric limits does not imply identical admitted source sets.
General lexical JSON and region nesting are bounded by 64. Only slot 8 of an
exact ten-slot protocol-function row in the definitions table is exempt from
ordinary lexical JSON depth; its origin is strictly decoded using the separate
typed tree limits above, with up to two arrays per term level. The input's MLIR
nesting preflight still applies. Helper reference depth is the
longest reference path in **edges**, with a leaf at 0 and a maximum of 64.
The writer counts the emitted graph: a scoped request contributes an edge to
its derived declaration, which contributes another edge to each referenced
helper or domain. This matches the structured reader's retained declaration
graph. The independent native observer instead counts actual native references;
its graph has no export-local declaration nodes. Both inspect dormant references
and shared suffixes without expanding calls. Their depth capacities are distinct
from the observer's one-based reached invocation depth above.
See the [formal contract](../../../lean/docs/spec/structured-source.md). All failures
produce diagnostics rather than a partial successful snapshot.

Export and independent import check a deliberately limited logical profile.
They do not establish frontend translation, participant projection, finite
algorithm selection, native provider arithmetic, runtime resource policies or
protocol security. A later compiler correctness result must relate the exact
source and target subjects under explicit observations and capacity premises.

### Total shape expressions

`["index.less"]` takes two indices and returns their strict natural comparison.
`["vector.length", field-domain]` takes a field vector and returns its length;
its native operation is `data.dim` on axis zero. Other axes or collection kinds
are outside this descriptor. `["index.power_of_two"]` takes `(n, r)` and returns
whether `n = 2^r` over naturals. All three are total Math expressions. Within the
native unsigned 64-bit index ABI the last predicate equals
`r < 64 && n == (1 << r)`. Its executable recipe enumerates the 64 representable
powers with safe constant shifts; it does not construct an unbounded power or
shift by a runtime exponent.

### Total vector prefix restriction

The exact descriptor `["multilinear.restrict_prefix", field-domain]` represents
`algebra.multilinear_restrict_prefix`. It takes two `["vector", field-domain]`
operands in `(values, point)` order and returns one vector in that field.
It has no site, attributes, parameters or regions and occurs only in Math and
protocol calculations. The field must resolve against the unit's catalogue.
Missing or extra descriptor slots, unknown domains, mismatched ports, sites,
regions and Local use refuse; there are no alternative spellings.
Its [total meaning](../domains/polynomials.md#total-vector-prefix-restriction)
has no vector-shape premise. This addition keeps format version zero and
updates the native producer and strict Lean reader together.

## Native row associations

The C++ `exportStructuredSource` result contains the exact snapshot `bytes` and
an `associations` table produced during the same row emission. The command
`protocol-structured` continues to write only those snapshot bytes. Associations
are proposals outside the admitted snapshot; they neither alter its identity nor
prove correspondence with source or native execution.

Each association names a row by an array-index path from the snapshot root and
the original MLIR operation that produced it. For example, `[7,d,9,1,i]` selects
instruction `i` in definition `d`; appending `[3,r,2,1,j]` selects instruction `j`
in its region `r`. The function row selects its ports, so argument/result/operand
positions are obtained from that actual row rather than a second semantic graph.
Associations also cover relation, binding and domain declarations, domain
constructors and results, contracts, nested regions and block terminators.
Retained source-declaration rows use `[10,table,index]`, where table zero is
records and table one is protocol ports. Their producer is the `protocol.module`
carrying the checked `source_declarations` attribute; this does not invent an
executable declaration operation or assert an exact authored-node match.
Catalogue rows are installed meaning, not emitted source operations.

The producer distinguishes direct rows, decoded scoped execution and derived
computation declarations. Scoped regions name their actual closed helper;
repeated uses have separate coordinates even when they share that helper.
Scope, transfer and failure plumbing omitted from the structured profile does
not acquire an invented executable row. An association to an operation records
the producer's derivation; it does not assert a one-operation semantic rewrite.

An original range selects the operation-name bytes in the supplied original,
with exclusive end and one-based line/column. It comes from MLIR's assembly
parser state, independently of `loc` annotations. A parser-inserted operation
with no written definition has an absent range. The table owns its strings and
coordinates after the MLIR context and parser are destroyed. Retained table
storage is bounded before each copy, in addition to the snapshot's existing
input, depth, instruction and byte limits. Failure returns no partial result.

These coordinates renew when the export changes. Source-level binding,
specialization and role proposals still require their own retained checking
facts; a lexical range is not an authored AST identity or semantic evidence.
