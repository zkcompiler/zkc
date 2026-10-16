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
graph; helpers cannot call the selected root. The independent
[formal admission contract](../../../lean/docs/spec/structured-source.md)
defines the Lean interpretation.

## Envelope and types

The current format is an exact tagged array, `zkc.structured-source/0`:

```text
[format, "original", source-sha256, entry-name, domains, relations, bindings, definitions]
```

`source-sha256` is `sha256:` followed by 64 lowercase hexadecimal digits, hashing
the exact supplied MLIR bytes. It identifies those bytes; it is not a proof of
their semantics or of export correctness. Every record below has the exact
displayed arity. Unknown tags, extra fields and unrepresented native attributes
are refused.
All eight slots are required, including empty tables. Each declaration category preserves its native encounter
order. There is no cross-category declaration-order field.

| Type | Native interpretation |
|---|---|
| `["bool"]` | `i1` |
| `["index"]` | unsigned 64-bit index |
| `["field", domain]` | nominal scalar field |
| `["vector", domain]` | immutable vector over that field |
| `["group", domain]` | nominal group |
| `["service", contract]` | owner-local reusable service reference |

The admitted domains are `bls12-381.fr` and `bls12-381.g1`, whose associated
scalar field is `bls12-381.fr`. The only service contract is
`random.bls12-381.fr/0`, with method `draw`. Services occur only at protocol
input roots and as the actual query handle operand. The native
[service contract](../runtime/services.md) requires singleton ownership and
permits same-owner root aliases; services cannot be selected, restricted,
exchanged, returned, passed to Math/Local helpers, or bound as statement data.
Affine resources, variants, matrices, general arrays, arbitrary kernels and other
unlisted operations require a separately specified extension.

## Declarations

```text
["domain", name, input-types, ["elements", container-argument]]
["domain", name, input-types, ["indices", container-argument, 0]]

["function", name, kind, visibility, input-types, output-types,
 interface, preconditions, origin, body]

interface := ["protocol", role-names, input-scopes, output-scopes]  # protocol
           | []                                                  # math/local

["relation", name, visibility, kind, key, revision,
 input-types, output-types, purposes]

["binding", name, contract, domain-arguments, implementation]

["finite", name, visibility, input-types, output-types,
 domain-name, step-name, predicate-name]
```

A domain body consists of exactly one supported constructor and its matching
yield. Additional constructors are refused, including unused ones. The selected
input is a vector; other inputs remain part of the domain and callback ABI.
Elements yield one field value; indices yield one index. Only axis zero is
supported.

Function `kind` is `protocol`, `math` or `local`; visibility is `public` or
`private`. Each protocol has 1 to 16 unique nonempty native role strings. Every
port has a nonempty scope drawn from that protocol's own roster; scope counts
match the signature. Owner references are local to that roster, including in
unused protocols. The writer retains native names without reconstructing
authored names or imposing the selected root's roster on other definitions.

Relations are non-callable metadata, retained even when unused. The declaration's
`kind`, `key` and `revision` are opaque exact strings. Native verification checks
their validity and consistency, the ordered signature, and each input purpose
(`parameter`, `statement`, or `witness`). A relation has one Boolean result.
Retaining a Math formula and a relation does not associate them: generated symbol
names are not formula bindings. Any such association requires the separately
checked language interface.

Operation bindings are non-callable metadata for `local.binding`, retained and
checked even when unused. The exact represented native attributes are
`sym_name`, `contract`, `arguments`, and `implementation`; no signature, body,
visibility, or execution parameters are invented for them. Names match ASCII
`[A-Za-z_][A-Za-z0-9_.-]*` and have at most 256 bytes. Index contracts require
empty domain arguments; vector and field contracts require exactly
`["bls12-381.fr"]`. The implementation selector must be the explicit empty
string. Selected implementations and contracts outside the catalogue below are
refused, including on dormant declarations. Distinct binding names with the
same metadata remain distinct retained rows.

Math preconditions are exact arrays
`["index_bound", index-argument, container-argument, 0]`. Other relation
annotations are refused. Protocol and Math origin is `[]`; Local origin is
`[origin-name, [[key, value], ...]]`, preserving the ordered `logical_origin`
bindings without flattening them or substituting the helper symbol.
Bindings have unique nonempty keys and nonempty values, with at most 128 pairs.
The native verifier validates binding values against installed and canonical
static identities. Lean retains these values as opaque metadata and checks their
shape and uniqueness; it does not independently reproduce that identity registry.
Math helpers are private.

A finite declaration represents `local.finite_fold`. The empty predicate name
means no predicate. There is no implicit Unit leaf for an empty state or result.
The [finite ABI](../ir/finite.md) is retained: operands are `A ++ S ++ C`, the
step receives `S ++ I ++ A ++ C`, and the predicate receives `I ++ A ++ C`.
Callbacks are private and have the required Math or Local kind.

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
| `["exec", native-operation, binding-name, parameters]` | checked Local primitive occurrence from the catalogue below |
| `["field.constant", domain, decimal-string]` | canonical scalar constant |
| `["field.add" / "field.subtract" / "field.multiply", domain]` | two fields to one field |
| `["field.equal", domain]` | two fields to Boolean |
| `["group.identity", group]` | group identity |
| `["group.add", group]` | two groups to group |
| `["group.scale", group, field]` | group then associated scalar field to group |
| `["group.equal", group]` | two groups to Boolean |
| `["bool.constant", value]` | Boolean constant |
| `["bool.and" / "bool.or" / "bool.xor" / "bool.equal" / "bool.not_equal"]` | two Booleans to Boolean |
| `["select", type]` | Boolean and two equal-typed values to that type |
| `["bounded_at", domain]` | vector and index to field, with exact bound obligation |
| `["call", name]` | ordinary Math helper call |
| `["apply", name]` | Local helper or finite declaration call |
| `["local_call", name, participant]` | Protocol call to a Local helper with exact owner |
| `["fold", domain, step, predicate]` | total Algebra fold |
| `["if"]` | Local conditional over closed captures |
| `["for"]` / `["for_condition"]` | Local counted control |
| `["guard", participant]` | Protocol guard with exact owner; false rejects |
| `["restrict", role-names]` | same value restricted to the retained scope |
| `["exchange", sender, receiver]` | sender alias and independent receiver value |
| `["draw", owner, field]` | query the actual service handle operand; one field result |
| `["statement", relation, selectors, acceptance-index]` | ordered entry operands; zero results |

Every operand, result and region interface is checked against the selected
descriptor and referenced declaration. A same-typed result permutation can be
a valid different program. It is preserved rather than classified as a type
error. A bound for a different same-typed vector does not authorize a read.

A statement's selectors are actual native role strings, one per operand. Native
verification checks that each operand is an entry argument available at its
selector, with the exact relation input signature. The acceptance index selects
a Boolean result of the enclosing protocol; zero and nonzero indices are
preserved. A statement does not evaluate a relation, assert satisfaction, or
identify different participants' copies of an acceptance result.

Ownership is checked independently of operand types:

| Body kind | Admitted instructions |
|---|---|
| Protocol | Pure index constant/equality and field/group/Boolean operations, select, Math call, Algebra fold, Local call, guard, restrict, exchange, draw, statement |
| Math | Pure index constant/equality and field/group/Boolean operations, select, bounded read, Math call, Algebra fold |
| Local | Boolean constant, checked primitive execution, Local apply, conditional and counted control |

The descriptor can represent selection of any admitted value type. The current
native mathematical verifier admits Boolean, scalar-field and group selection in this
profile; vector and index selection are not yet native export paths.

Only Local bodies may end in an explicit stop. A guard retains the owner of
the original `protocol.guard`; projected `local.guard` is outside this source
stage. Maps, mathematical realizations, protocol application and protocol
repetition remain outside this profile.

Multi-role protocols cannot use Math folds or bounded reads, including through
retained Math helpers. Those combinations require additional partial-component
semantics. Existing single-role finite programs and owned Local finite work
remain supported. Math calls propagate each input's availability through the
actual helper body: `first(x,y) = x` does not require `y` at the same participant.
Native verification also checks availability of unused intermediate expressions.
Local calls require all inputs at their owner, execute there even with zero
results, and do not execute at other participants. Restriction and declared
output scopes never erase preceding effects or stops.

## Primitive execution

An `exec` descriptor retains both the native operation kind and binding name,
plus the exact ordered array of string parameters. It has zero regions and a
required nonempty site, unique within its enclosing Local definition. Each use
checks kind/contract agreement, nominal domain arguments, full ordered operand
and result types, parameters, and Local ownership. Binding names confer no
semantics by themselves. The exporter reuses the native logical catalogue for
these ABI checks; the test reference independently admits this closed table.

Here `I` is index, `B` Boolean, `F` Fr, and `V` a vector over Fr. The operation
spellings are exact, not an extensible prefix convention.

| Native operation | Binding contract | Inputs → outputs | Parameters |
|---|---|---|---|
| `algebra.exec.index_constant` | `index.constant` | `[] → [I]` | `[n]` |
| `algebra.exec.index_add` | `index.add` | `[I,I] → [I]` | `[]` |
| `algebra.exec.index_sub` | `index.sub` | `[I,I] → [I]` | `[]` |
| `algebra.exec.index_mul` | `index.mul` | `[I,I] → [I]` | `[]` |
| `algebra.exec.index_div` | `index.div` | `[I,I] → [I]` | `[]` |
| `algebra.exec.index_mod` | `index.mod` | `[I,I] → [I]` | `[]` |
| `algebra.exec.index_equal` | `index.equal` | `[I,I] → [B]` | `[]` |
| `algebra.exec.index_less` | `index.less` | `[I,I] → [B]` | `[]` |
| `algebra.exec.vector_empty` | `vector.empty` | `[] → [V]` | `[]` |
| `algebra.exec.vector_length` | `vector.length` | `[V] → [I]` | `[]` |
| `algebra.exec.vector_sum` | `vector.sum` | `[V] → [F]` | `[]` |
| `algebra.exec.vector_split` | `vector.split` | `[V] → [V,V]` | `[]` |
| `algebra.exec.vector_append` | `vector.append` | `[V,F] → [V]` | `[]` |
| `algebra.exec.vector_equal` | `vector.equal` | `[V,V] → [B]` | `[]` |
| `algebra.exec.field_equal` | `field.equal` | `[F,F] → [B]` | `[]` |

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
`algebra.exec.field_equal`.

Ordinary source wrappers capture the unchanged `multilinear::has_shape`,
`table`, and `halves` helper closures, including the private rows loop and
short-circuit guards. `table` checks shape; `halves` itself checks positive
dimension and split length, so its stronger shape interpretation requires the
constructor premise. An independent append/count example covers vector and
integer operations. The complete frontend original is exported without slicing
or preparation; unsupported dormant native declarations still refuse.

## Limits and evidence

The independent native SSA test executable retains its closed invocation:
`zkc-structured_reference-test FILE SYMBOL INPUTS_JSON`. Its single-role scalar
and finite inputs and outputs are unchanged. Open executions use a distinct
command and exact request:

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
length to 4096 and loop bounds to 2^20; evaluation depth is 64. Capacity failures
are explicit `structured-reference-capacity` diagnostics, not simulated native
stops. This is bounded test evidence, not an interpreter correctness theorem.
Vector result lengths are checked before allocation. Sum, split and equal-length
equality charge one additional work unit per element; append charges its output
length. Length itself is constant work. An input/reply longer than 4096, an
append exceeding that bound, or insufficient observer work produces a capacity
diagnostic. A malformed typed reply instead stops refused without consuming it.
The observer's finite vector bound makes the logical unrepresentable-length
exhaustion branch unreachable; it does not replace it with source refusal.

The writer bounds source bytes to 16 MiB, the complete exported file (including
its final newline) to 1 MiB, strings
to 512 UTF-8 bytes (binding names to 256 ASCII bytes), domains, relations,
bindings and definitions to 128 each, signatures to 512
positions and total instructions to 4096. The instruction count includes nested
bodies and one fold per finite declaration; it excludes terminators and domain
constructors. Lexical JSON and region nesting are bounded by 64. Helper reference
depth is bounded by 64. References are derived from stored instructions, with
at most two helper references per instruction; shared calls are not expanded for admission.
See the formal contract. All failures
produce diagnostics rather than a partial successful snapshot.

Export and independent import check a deliberately limited logical profile.
They do not establish frontend translation, participant projection, finite
algorithm selection, native provider arithmetic, runtime resource policies or
protocol security. A later compiler correctness result must relate the exact
source and target subjects under explicit observations and capacity premises.
