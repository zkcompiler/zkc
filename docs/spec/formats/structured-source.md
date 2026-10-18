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

## Envelope and types

The current format is an exact tagged array, `zkc.structured-source/0`:

```text
[format, "original", source-sha256, entry-name, domains, relations, bindings, definitions, contracts]
```

`source-sha256` is `sha256:` followed by 64 lowercase hexadecimal digits, hashing
the exact supplied MLIR bytes. It identifies those bytes; it is not a proof of
their semantics or of export correctness. Every record below has the exact
displayed arity. Unknown tags, extra fields and unrepresented native attributes
are refused.
All nine slots are required, including empty tables. Each declaration category preserves its native encounter
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
`random.bls12-381.fr/0`, with method `draw`. Services originate at protocol
input roots and may be query handles or actual protocol application arguments.
The native
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
 input-types, output-types, purposes, formula]

["binding", name, contract, domain-arguments, implementation]

["finite", name, visibility, input-types, output-types,
 domain-name, step-name, predicate-name]

["realize", name, input-types, output-types, math-helper]
["map", name, input-types, output-types, math-helper, rowwise]
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
`formula` is null or the exact symbol of a defined Math helper in this unit.
For `kind = "zkc.language.formula/0"` the link is required and its full ordered
input/output signature must equal the declaration's signature. Other kinds use
null. A Local function cannot satisfy a Math formula link. Names and hashes do
not infer this association; the original `relation.declare` owns it. Structural
association supplies no totality, relation adequacy or security proof.

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
Native protocol formation currently permits no explicit `sym_visibility`
attribute, including an explicit `public`; its retained visibility is the
default `public`. The general function record does not override that formation
restriction or impose the Math helper's private-only rule on protocol calls.

A finite declaration represents `local.finite_fold`. The empty predicate name
means no predicate. There is no implicit Unit leaf for an empty state or result.
The [finite ABI](../ir/finite.md) is retained: operands are `A ++ S ++ C`, the
step receives `S ++ I ++ A ++ C`, and the predicate receives `I ++ A ++ C`.
Callbacks are private and have the required Math or Local kind.

Realization and map records retain original `local.realize` and
`algebra.map_realize` declarations. Their exact native attributes are `sym_name`,
`function_type`, `helper`, and, only for map, `rowwise`. They have no operands,
results or regions. No visibility, origin, premise, site or function body is
invented. The helper is an exact flat reference to a private defined Math sibling.
The wire retains nonempty symbol strings within its 512-byte bound. Native Local
formation additionally requires preparation names to match ASCII
`[A-Za-z_][A-Za-z0-9_.-]*` within 128 bytes; the separate binding limit is 256.
Math helper names retain the ordinary Math symbol bounds. Every declaration is
checked, including unused ones.

A realization has exactly the helper's full ordered input/output ABI, including
unused inputs and zero or multiple results. Its derived Local meaning is one
ordinary invocation of that helper. The original declaration remains distinct
from the derived body. Initially the entire transitive helper closure must have
empty preconditions and use only the admitted pure field/group/Boolean/index
operations, select, Math calls and return. Finite operations and bounded reads
are refused in this closure even when the native realization is valid. Other
Math functions retain their existing finite profile.
Native formation requires call-site evidence for nested helper premises, even
on dead calls. It can accept a premise discharged by a finite index callback
below an unconditional realization root. Such a structured negative also hits
the finite-work exclusion; it does not isolate the transitive-premise check.

A map root takes only `bls12-381.fr` scalars and returns exactly one such scalar.
`rowwise` is a Boolean array with exactly one entry per input and at least one
true. A true position lifts that scalar to a vector; a false position remains a
scalar broadcast. The result is one vector. Every transitive instruction,
including dead calls and unused results, must belong to that field's ring
fragment: constants, add, subtract, multiply, Math calls and return. Nested
callees may return zero or multiple scalars; the one-result restriction applies
only to the root. All helper preconditions are empty. Equality, selection,
indices, groups, finite operations and other fields are outside this map profile.

Both native tools run native formation before their separate structured checks.
Native formation owns the map ABI, mask, helper identity and transitive ring
fragment rules, including dead operations. Each structured reader repeats these
checks, but malformed-map controls through these tools observe the native
formation refusal first; they do not isolate the redundant structured closure
checks. The structured Fr-only restriction and structural capacity limits remain
independently observable. Native formation accepts a wider realization fragment
than the conservative structured closure above.

Preparation declarations are invoked only by `local.apply` in a Local function.
`protocol.local_call` requires an actual Local function, so an ordinary wrapper
is necessary. Math calls cannot invoke preparations. Finite callbacks still
require actual private functions of the appropriate kind; a derived Local
meaning does not change the original native kind.

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
| `["field.constant", domain, literal-string]` | canonical scalar constant: a decimal residue, or for a binary field a [bit-pattern literal](../domains/values.md#bit-pattern-literals) |
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
| `["apply", name]` | Local function, finite, realization or map declaration call |
| `["local_call", name, participant]` | Protocol call to an actual Local function with exact owner |
| `["protocol_apply", name, role-names]` | Retained static protocol application with positional role substitution |
| `["protocol_repeat", carried, maximum, roles, carried_roles]` | Retained protocol repetition with one isolated optional-state callback |
| `["fold", domain, step, predicate]` | total Algebra fold |
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
| Protocol | Pure index constant/equality and field/group/Boolean operations, select, Math call, Algebra fold, Local call, protocol application and repetition, guard, restrict, exchange, draw, entry statement |
| Math | Pure index constant/equality and field/group/Boolean operations, select, bounded read, Math call, Algebra fold |
| Local | Boolean constant, checked primitive execution, Local apply, conditional and counted control |

The descriptor can represent selection of any admitted value type. The current
native mathematical verifier admits Boolean, scalar-field and group selection in this
profile; vector and index selection are not yet native export paths.

Only Local bodies may end in an explicit stop. A guard retains the owner of
the original `protocol.guard`; projected `local.guard` is outside this source
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
A callback ending with `local.stop` instead reaches `mathematical-formation`
because it does not yield the carried interface.

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
its own `mathematical-formation` depth and collision obligations. Lexical JSON
depth 64 is a distinct wire-profile bound, not permission for 64 stored nested
callbacks. Reference-graph depth, application summary depth and observer depth
retain their existing definitions.

Complete unchanged repeat and nested-repeat sources, an ordinary service-order
wrapper, and the complete original Reduction/Sumcheck units can be exported and
admitted. Their native reference observations are bounded evidence. Full
Sumcheck symbolic equations, affine resource models and production correspondence
are separate obligations; no protocol-specific intrinsic supplies their meaning.

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

## Map and realization execution

The independent reference invokes the exact retained Math helper through its
existing SSA evaluator. It does not dispatch a production kernel, extract a
polynomial for another evaluator, or assign meaning by helper name. Realization
passes every argument and returns every result in order. Owned Local calls are
strict even for an unused projection input or a zero-result invocation.
Native missing-input controls observe strictness at `protocol.local_call`, before
entering its Local body. They do not separately exercise a direct optional
derived map operation or the inner preparation invocation presence check.

Map first measures the first row length, stopping `exhausted` if it is not below
2^64. It then visits each remaining row input in argument order, measures and
checks representability, and stops `refused` at the first unequal length.
All rows are checked, even when unused by the formula or when the first is empty.
An earlier mismatch precedes a later unrepresentable length. After that prefix,
rows are evaluated in increasing order with the complete scalar tuple in original
argument order, selecting each row element or scalar broadcast. Equal empty rows
return the empty vector without invoking the helper. Admission has nevertheless
already checked the entire unit and every helper body.

The derived operation has no authored internal site; shape refusal uses the
invoking `local.apply` site. Discarding its result cannot discard that stop or
allow a subsequent interaction. Nonowners skip owned Local work. Native map
preparation instead inserts `control.require` guards with generated sites and
backend failure `rejected:require`. Relating that failure to source `refused`
requires an explicit observation/site mapping; the raw codes and generated
sites are not equated here.

Ordinary wrappers capture unchanged `multilinear::fix_first` and `fix_prefix`,
including their table constructor and values/variables/width projections.
`fix_prefix` uses existing Local finite folds. An independently authored Fr linear
combination covers ordered broadcasts and unused scalar/row arguments. The native
library's KoalaBear Ext8 Combination remains outside this Fr-only profile.

Structured admission checks retained SSA, without production formula expansion.
Native language emission additionally checks expanded Ring eligibility; native
preparation can reject a handwritten map for Ring depth even after ordinary
formation succeeds. Structured admission alone does not claim that eligibility.

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
to 512 UTF-8 bytes (binding names to 256 ASCII bytes), domains, relations,
bindings and definitions to 128 each, signatures to 512
positions and total instructions to 4096. Operand references index the lexical
value list and are also at most 4096. The instruction count includes nested
bodies and one derived instruction per finite, realization or map declaration;
it excludes terminators and domain
constructors. The independent native reference enforces the same 4096-instruction
admission budget, independently of runtime fuel and without expanding calls.
Lexical JSON and region nesting are bounded by 64. Helper reference depth is the
longest reference path in **edges**, with a leaf at 0 and a maximum of 64 in both
native readers. A preparation-to-Math-helper reference contributes one edge,
as do calls to Local wrappers and preparations. References are derived from
stored instructions, with at most two helper references per instruction; shared
calls are not expanded for admission.
See the [formal contract](../../../lean/docs/spec/structured-source.md). All failures
produce diagnostics rather than a partial successful snapshot.

Export and independent import check a deliberately limited logical profile.
They do not establish frontend translation, participant projection, finite
algorithm selection, native provider arithmetic, runtime resource policies or
protocol security. A later compiler correctness result must relate the exact
source and target subjects under explicit observations and capacity premises.
