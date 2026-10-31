# Closed mathematical protocols

This profile defines a closed, straight-line common protocol containing total
mathematics, messages, owner-local executable calls, immediate guards and a
retained statement interface.
Each role computes its own values and ordered actions; receives supply actual
role-local inputs, and guards can stop the reached execution prefix.
[Relations and terminals](../relations.md) define the retained statement and
explicit terminal checks; [realization](../realization/representations.md) states
the obligations of a claimed implementation relation. The formal
[interaction model](../../../lean/docs/spec/semantics.md) is a
parameterized counterpart, not an established interpretation of this IR.
Implementation coverage and deferred connections belong to [status](../../status.md).

## Common representation and role components

`protocol.func` is an isolated, single-block symbol inside the isolated
`protocol.module` symbol table with `#protocol.profile<protocol>`. The common
mathematical profile has no participant execution-contract selector.
It declares a function type, distinct named roles, and a nonempty role set for
every input and result port. Its body ends with `protocol.return`. An input of
logical type `T` exposed to roles `A` denotes a family `(r in A) -> Value(T)`.
Different roles may hold different values. Availability asserts neither public
agreement nor secrecy. A role's participant retains every advertised input even
when its executable result does not depend on that input.

Source-emitted protocols also carry `origin`, the logical qualified NFC
template path and declaration-ordered named static arguments in the public
[typed term grammar](../formats/structured-source.md#definition-origins).
General native IR may omit this attribute; structured export requires it on
every protocol definition. A present origin is verified independently of the
body. Language correspondence recomputes it from the checked declaration.
Binding a callee through its origin and proving its body equal are separate
obligations.

Mathematical operations use ordinary logical types and SSA edges. Interface
attributes and explicit `protocol.restrict_roles` operations retain declared role
boundaries. Intermediate availability is derived, never supplied as a trusted
summary. A total operation's availability is the intersection of its operand
availability; an operation with no dependencies would be available at every
declared role. A restriction selects a nonempty subset of an existing value's
components. It neither communicates nor changes their values.

`protocol.assemble_roles` is the pointwise counterpart of restriction. It has
one ordinary total, shared, non-affine input per distinct named role, all of the
same type, and one result. At role `roles[i]`, the result is precisely that
role's component of operand `i`; elsewhere it is absent. Every selected component
must already be available. The nonempty role list is checked even for unused
assemblies. Assembly grants no equality, secrecy, communication or authority.
It cannot assemble services, custody values or logical oracle handles. This
supports ordinary carriers after oracle realization without a native oracle
object. Projection selects the actual operand separately at each role, including
loop captures, and erases assembly before executable lowering.

Every internal operation must have an admitted meaning and at least one
available component, including unused operations. A returned port's declared
roles must be a subset of its value's availability. Simplification may remove a
dependency; it does not widen declared ports. A restriction still used by an
action or result retains its selected components until projection; an unused
restriction can be discarded after original admission. Admission checks unused
restrictions before optimization. Restrictions have formation meaning and no
runtime state transition; projection can erase them after checking owned uses
and declared ports. The retained original for correspondence is the immutable
pre-pass source, distinct from a projector input that may already be optimized.

A common SSA value denotes a whole role family. A rewrite based on a guard or
exchange fact valid at only one role cannot replace that whole family. Apply
such facts after participant projection or under a separately admitted
component-selective transformation.

This flat representation permits ordinary SSA transformations without an
isolated region around each expression. The choice and its alternatives are
explained in [the rationale](../../rationale/mathematical-ir.md).
No intermediate located common program is required by this profile.

## Logical oracle kinds and handles

`#protocol.oracle_kind<"table", [T]>` associates ordinary table data with a
query and answer type. Field rows use the matching field vector, group rows
use the matching group vector, unsigned 64-bit index rows use `algebra.indices`,
and other admitted total data rows use `data.sequence<T>`. A table query has
logical type `ui64` and its answer has type `T`. Rows must be canonical total,
shared, non-affine logical data; capabilities, physical representations and
oracle handles cannot be rows. Complete logical type bounds apply to the
associated collection as well as to its row.

An optional second argument, an unsigned 64-bit integer attribute, fixes the
exact number of rows. Omission denotes a runtime row count; a present zero
specifies an empty table. The sized kind retains this refinement even when its
associated collection type has a runtime length. The kind owns named immutable
shape dimensions: `table` has `rows`. A table query succeeds only when its position
is smaller than the actual row count, independently of any static maximum.
An invalid position stops at that query occurrence before an answer or generated
opening work. An empty table has no successful query. Total ordinary collection
lookup with a default value does not implement this stopping contract.
Realization must preserve shape agreement, this refusal and the reached prefix. Power-of-two restrictions and
native capacity bounds belong to the selected realization and execution
admission. Unknown kinds, including reserved polynomial kinds, refuse.

`!protocol.oracle<K>` is a logical handle for checked kind `K`. Its type fixes
the Data/Query/Answer associations, not a commitment scheme, physical storage
or occurrence anchor. Equal data does not identify anchors.
`!protocol.oracle_sequence<K, maximum>` is a bounded ordered logical handle
container; zero permits only an empty sequence. The bound describes a logical
natural and grants no allocation or execution budget. Neither handle type has
an ordinary native binding or message codec, and `data.sequence` cannot wrap
one to obtain such permissions. Oracle operations and realization are separate
admission boundaries; registration of these types grants no executable effect.

### Internal anchor storage

Realization may represent logical anchors with ordinary, immutable data. In the
current private lowering, a reference carries a constructor ordinal and an
instance ordinal. Each constructor and role has a separate append-only store.
Equal payloads never merge constructions. Splitting a port into components or
rebinding those components preserves its reference instead of allocating again.
Static shape erasure preserves the reference type and the stored actual shape.

Each record retains its enclosing repeat indices, named dimensions, structural
leaf count and role payload, in that order. An instance ordinal alone does not determine nested
iteration coordinates when trip counts vary. Virtual payloads retain actual
child references and ordinary parameters. Ideal table delivery gives receivers
the table; a Merkle receiver stores the root, while data and opening state stay
with the holder. Virtual anchors never select a commitment scheme.

The allocation primitive reads the old store length, packs the supplied record,
appends it, and returns the constructor/old-length reference with the new store.
Its independent check reads actual resolved bindings, ordered outcomes and SSA
operands. It does not establish that supplied coordinates, dimensions or payloads
come from the source occurrence; the complete source-to-realization check must
establish that association. Type, work and capacity limits are compiler resource
refusals, separate from the logical query-domain stop. No native oracle carrier
or runtime interpreter is introduced by this representation.

The lookup primitive checks that the reference names the selected constructor
before reading its instance from that role's store. It returns the stored
coordinates, dimensions and payload in their declared order. Its reader checks
both variant destructuring regions, the exact tag comparison, instance operand,
resolved sequence binding and returned fields. A forged tag or absent instance
cannot select a different anchor. The surrounding realization still must choose
its constructor from the runtime reference and bind the correct store.

The generated table-read primitive compares the requested position with the
supplied actual row count, requires that comparison, and only then reads the
collection. Its independent reader checks the precise comparison operands,
ordered stop and collection binding for every supported row carrier. A longer
backing collection cannot make an out-of-domain query succeed. Binding the data
and actual shape to the source anchor remains the complete realization's duty.

Pure virtual-query lowering separates each declaration into ordinary total
position functions and one answer function. Position functions take the ordinary
parameters and outer position; the answer function additionally takes every
child answer in declaration order. The retained query inventory identifies the
source formal, kind and occurrence site, including duplicate queries and unused
answers. Helper dependencies follow actual return values, so an ignored helper
argument does not create a false dependency on an earlier answer. An independent
reader derives a closed substitution recipe from the frozen declaration and
checks exact operations, attributes, operands, nested regions, return values and
the complete ordered query inventory. Extra pure operations and alternative
helper indirection are not part of this representation, even when they compute
the same value. These functions neither query nor check
query domains: the surrounding realization must validate the outer domain and
then execute each reached child query in order before calling the answer
function. This pure substitution check does not establish the surrounding
control lowering or its association with actual anchors.

Structural query capacity is derived from the prepared entry. A base table
contributes one leaf and one node; a virtual contributes one node plus the
complete ordered expansion of each declared query, including duplicates and
unused answers. Handle sequences join the sizes of possible selected anchors;
component rebindings and shape erasure retain the bound. Repeat analysis joins
zero-trip and backedge values, including nested loops, and may stop at a
post-fixed point. It never evaluates positions, answers, data or admissibility.
An unrepresentable bound or exhausted analysis work refuses compilation rather
than adding a logical premise or truncating a query. These bounds do not select
an actual anchor, check an emitted controller or establish a simulation.

### Ordinary query continuations

The private table controller specializes the prepared entry's finite constructor
vocabulary. Its state contains the current constructor, instance and position,
the continuation tag and instance, the answer kind and a phase, followed by typed
answer slots and append-only continuation arenas. Immutable anchor stores are
captures. No logical handle or oracle provider enters native execution.

`initialize` starts a query. `advance` follows actual references in declaration
query order, checking the current anchor's actual domain before evaluating a
child position or suspending at a base-table request. `resume` accepts an answer
only in the request phase, for its exact kind and five request/continuation
coordinates. `finish` requires completion of the root answer. A continuation
retains the parent's position, instance and already obtained child answers;
unused and duplicate child queries are still executed. Empty answer slots avoid
inventing a default inhabitant of an arbitrary answer type.

The exact leaf count is derived at construction from actual child references:
one for a base table, zero for an empty virtual declaration, and the sum of every
ordered child-query count otherwise. The same immutable record stores it. Count
helpers perform reference lookup and checked index addition without evaluating
positions, domains, answers or authentication. Their independent body check
compares the recurrence with the declaration's complete ordered query inventory.
Binding this derived value to the same source allocation remains the complete
stage's responsibility. A role's count is its own family component; availability
does not assert agreement between roles.

The checked structural capacity bounds advancement by `2 * nodes + 1` transitions
and local evaluation by `leaves + 1` advancement rounds. Each round must suspend
or complete; exhausting the bound cannot publish a partial answer. The final
round executes any trailing zero-query virtual children, including their domain
checks. Local evaluation exists only when the role retains every base table;
a Merkle receiver instead needs the surrounding common opening exchange.

For direct field tables, ordinary scoped Merkle primitives map a logical query
`q` and dynamic row count `N` to physical height, leaf and payload slot. They
require a positive power-of-two `N` and `q < N`. Individual grouping has width
`W = 1`; antipodal grouping requires `N >= 2`, has `W = 2` and places logical
rows `i` and `i + N/2` in one leaf. With `H = N/W`, the slot is `q/H` and the
logical leaf is `q % H`. Optional bit reversal permutes exactly `log2(H)` leaf
bits after grouping and preserves the order within each leaf. Positive rows and
paired divisibility establish `H > 0`. Before leaf and slot arithmetic,
power-of-two admission checks `H & H.wrapping_sub(1) == 0` using total `ui64`
index operations. Natural order returns directly; bit reversal alone uses an
early-ending scoped loop. No field conversion or new runtime primitive defines
the query index. Invalid nonpower heights stop at the generated `admit_power`
guard, replacing the former loop's repeated `admit_span` check.

Commit preparation requires exactly `N` field values, transposes the two halves
for antipodal grouping and then applies the chosen leaf permutation. The selected
vector-commitment signature must match the exact field carrier. Authentication
checks the caller's root, width, physical height and mapped leaf against the
complete returned row and proof. Its successful guard precedes selection of the
logical payload slot. These primitive checks do not associate an opening state
or root with an original anchor. The enclosing realization still owns that
association, shape authority, role delivery and ordered query/batching semantics;
the cryptographic simulation is a separate obligation.

The independent primitive reader checks actual scoped control, SSA operands,
layouts, pure maps, domain guards, ordered frames and all helper bodies. It
neither invokes the emitter nor accepts a symbol name as body evidence. The
surrounding realization must derive the storage and capacity from the frozen
source, bind each call to its actual source operands, and connect each resumed
answer to the reached exchange and authentication. Resume coordinates are
ordinary data, not an authentication capability. These primitive checks do not
establish complete realization correspondence or the Lean simulation.

### Dynamic query windows

One sequence-packet engine implements remote queries. Per-query selection keeps
one source query and packet capacity one. Atomic selection groups at most 32
contiguous same-receiver queries whose actual handle and position operands
properly dominate the first query. An intervening operation ends the window;
an earlier answer cannot become a later discovery operand. Shared transport
also requires the same checked constructor, holder, store and response family.
A static source-derived bound covers the complete expansion. Exhausted analysis
or unrepresentable bounds refuse compilation without adding a source premise.

Discovery uses a separate answer-free continuation state. It may evaluate total
position maps and actual domains, but never an answer function. A false domain
marks a pending cut and retains the preceding valid demand prefix. It is not a
native failure and does not authorize skipping earlier authentication. Native
lookup, allocation, decoding and budget failures retain their own generated
positions. Discovery stops immediately at packet capacity without inspecting the
next window, including its next domain check.

Each positive packet is grouped by first use of the exact constructor, anchor
instance and physical leaf. Equal roots or equal data cannot merge identities.
The holder opens each physical request once. The receiver authenticates every
logical occurrence, in order, against its own request and retained root/shape,
even when occurrences share one response. Exact lengths and bounds are checked.
No evaluator resumes until the entire valid prefix authenticates. The bounded
linear first-use search has quadratic runtime cost; runtime execution meters
that work separately from compiler analysis and IR-generation allowances.

Replay follows the original evaluator and compares each next request with the
retained request before resuming from the evaluator's actual continuation.
Ordered end offsets bind every root's segment, including empty segments. Kind
numbers remain local to each controller. All source-root answers are returned
only after every root finishes in source order. Finishing also traverses trailing
zero-leaf children and their domains. An empty valid prefix in a positive round
runs these original finishes before any exchange so that the pending source
failure is preserved; an impossible successful empty round refuses internally.
Zero-total windows perform no communication and still finish every root.

Both participants compute structural round counts from their actual immutable
stores: one per leaf for per-query selection, and zero or one for an atomic
window. Counts do not prove that the leaves will be reached. A pending source
stop truncates execution at its defined boundary; no flush or cancellation
protocol is added. Private request/answer sequences and helper handles confer
no proof authority. The complete reader rederives source windows and checks
actual call sites, operands, stores, grouping outputs, segment offsets, round
counts, authentication-before-replay and final answer release. Independently
checking an unused helper is insufficient. Cryptographic realization and Lean
connection remain separate obligations.

Whole common realization accounts for every entry in its prepared subject.
Explicit deployment selection happens after complete source admission and
application expansion, before realization. It keeps the selected entries and
required companions, refuses dangling symbol uses, and retains the full authored
source separately. Realization cannot silently omit another entry from that
selected subject. Each oracle entry has its own constructor inventory and stores; shared
virtual definitions remain available until all referring entries are converted.
Ordinary declarations retain their exact bodies. The complete reader checks both
every converted entry and the union of generated helper dependencies, including
source-relative identities and authored/generated symbol collisions.

An escaping internal reference requires its immutable environment. The closed-unit
result representation preserves each original result position and role family,
replaces a receiver handle by its actual reference, and appends supporting store
leaves once per receiving role in declared-role/constructor order. An explicit
interface map associates each source result and role with its reference and store
positions. These are representation leaves, not additional authored results.
The reader derives the map from the original and checks final return operands,
including loop-updated stores. Repeated aliases share the same environment;
equal data does not merge distinct anchors. This representation grants neither
logical-handle serialization nor import of arbitrary graphs at another root.

The [realization record](../formats/oracle-realization.md) is the complete
native reader's input alongside the prepared original and actual common module.
It replaces process-local function references at that boundary with closed typed
metadata and exact symbolic generation slots. The reader derives constructors,
interfaces and occurrences independently; it does not regenerate MLIR. Empty
handle collections require no invented anchor or allocation: length is zero and
indexing checks its bound at the original occurrence, after earlier deliveries.

## Ordered oracle events

`protocol.oracle_send(data, shape...)` produces an `oracle<K>` handle at its
sender and distinct nonempty receivers. Data must have `K`'s associated type
and be available at the sender. Each `ui64` shape operand is available at every
participant in the send. `shape_names` lists every dimension exactly once in
kind order; `table` uses `["rows"]`. `shape_bounds` is a dictionary containing
exactly the dynamic dimensions with unsigned 64-bit maxima. It is explicitly
empty for a fully static kind. Missing, repeated or unknown names refuse.
Formation retains the obligation that actual data dimensions match the shape
operands and respect their static extents or dynamic bounds. Realization must
establish it before publishing the corresponding delivery.

Shapes may depend on initially bound inputs and closed total mathematics.
The dependency check follows both initial and yielded values of every reached
loop-carried dependency, including a producer later in the stored loop body.
Messages, service draws, oracle queries and scoped execution cannot determine
a shape in this profile. One shared work allowance bounds the check. Role
availability and shape provenance are separate requirements.

`protocol.oracle_query(handle, position)` is ordered at its declared owner.
The owner must have both inputs; the kind determines the exact query and answer
types, and only that owner receives the answer. Queries retain their unique
sites, including repeated positions and unused results. Sends allocate distinct
occurrence anchors even for equal tables. Both operations declare ordered reads
and writes through MLIR's existing effect resource, so generic CSE cannot merge
or discard them or treat them as pure mathematical expressions.

`protocol.oracle_forget_shape` removes static extent refinements,
retaining its answer type, actual handle, anchor and availability. It cannot
add a size or change kind. This operation is pure: merging the same conversion
of the same handle does not merge anchors or query events.

Logical handles remain unavailable to ordinary mathematical helpers, native
message codecs and executable endpoint policies. Oracle input/output ports use
the explicit data/anchor interface below; ordinary port admission does not grant
those permissions. Preparation remaps sender/receiver/query roles and compares the actual expanded bodies independently;
its simplification preserves the ordered events. Projection explicitly refuses
unrealized oracle operations before publishing a participant candidate. Structured
export and realization must recognize this vocabulary before it can proceed.
Registration and common formation do not supply an executable implementation.

### Oracle interface components

One source oracle port has two common interface leaves: ordinary data at its
holder and a logical handle or bounded handle sequence at its receivers.
For a single handle the data type is `K::Data`; for a sequence it is an ordered
ordinary sequence of `K::Data`. The receiver leaf retains the complete logical
type, including sequence capacity. Row bounds constrain every element and are
independent of capacity. Empty sequences are valid; order, multiplicity and each
actual anchor survive rebinding. These sequence interfaces are internal protocol
boundaries. Deployment-root sequence ingress has no installed contract and
refuses explicitly. `oracle_input(data, anchor)`
with `holder`, `receivers` and named `shape_bounds`, binds them
into the role family used by the body. A raw handle entry argument has exactly
one such binding, paired with a distinct holder data argument. Both leaves have
exactly the declared roles. Root bindings precede protocol effects; pure initial
shape computations may precede them. The anchor carries its expected shape,
which a receiver can observe without reading the holder's data. A binding checks
its kind or maximum against that shape and the holder data; the honest-input
condition relates their dimensions. It retains these checks even if unused.
There is no separately authored row-count port for the same oracle.

`oracle_components(handle) {holder, receivers}` is a pure view returning the
data and receiver handle for an application or return tuple. Every selected role
must have its component and the declared holder must hold every possible anchor.
An application supplies the paired results of the same component view, possibly
through role restrictions or a paired earlier application result. Equal data or
equal handle types do not authorize mixing anchors. For sequences, equal
lengths or element kinds likewise cannot establish pairing. The holder data is
a lazy interface view: transporting a virtual sequence does not evaluate all
its rows. Checked preparation forwards the original references and materializes
data only for an actual holder-data demand. A returned handle likewise
requires its matching data leaf with exact roles in the same result tuple.

Application expansion preserves the caller's anchor. Splitting, returning and
rebinding a component pair creates no new anchor. Only a root input binding
introduces the entry anchor. Its data/handle relation is a generated honest-input
condition, with no authored clause index. These operations preserve the operands
needed for that condition; the structured export and independent semantics must
carry it before a compiled oracle claim is available. In a proof realization the
receiver leaf is the selected public commitment and the holder leaf the witness.
Native formation alone does not prove that the commitment opens to that witness.

`oracle_shape(handle) {dimension="rows"}` reads one named immutable dimension
at each available component. Unknown dimensions refuse. For a static extent its
result is the type's count. For an unsized kind, using it as
an initially bound shape follows actual input/send/virtual dimensions, sequence
indices and loop backedges, substituting actual protocol-call operands. Root
input dimensions are initially bound; a callee's formal input does not make a
caller's later selection initial. In particular, selecting a differently sized handle
using a later answer does not turn its row count into initial configuration.

### Holder contents and bounded handle sequences

`protocol.oracle_contents(handle) {owner}` selects the immutable data at the
holder. Ordinary handle availability alone is insufficient: every possible
anchor reaching the operand must have that holder. A bounded backward dependency
check follows input and yielded values of loops, both inputs of sequence append,
selection from a sequence, and handle views. It does not choose the first
syntactic origin or assume a loop executes. Unknown producers refuse. Role
restrictions remain effective even when the underlying holder is known. The
operation is pure after admission; specification-side anchor selectors have
separate permissions and cannot authorize executable extraction at a receiver.

A bounded handle sequence is persistent and ordered. `oracle_sequence_empty`
constructs its empty value; `oracle_sequence_length` observes the length. Both
are pure and create no anchor. `oracle_sequence_append` preserves the exact kind
and maximum, appending the actual handle at the end. It stops when the sequence
is full. `oracle_sequence_at` checks its index against the current length and
returns that exact dynamic handle; it stops when out of range. A zero maximum
is a valid empty container, so append always stops. The maximum does not grant
allocation capacity or a native execution budget.

Append and selection name a nonempty, distinct role set and an ordered site.
Each role must have every operand. The result is available precisely at those
roles. Their stopping checks are ordered effects even when their results are
unused; generic simplification must preserve them. They neither send a handle
as a message nor perform an oracle query. Realization must preserve their order,
checks and dynamic anchor choice before projection. A static set of possible
origins justifies holder access; it never replaces runtime selection.

### Anchor contract selectors

A retained relation application may bind `["anchor", direction, native-port]`
to a data-typed formal. The selected boundary port must be an oracle handle;
its kind supplies the exact Data type. The actual input/output pair remains
subject to common oracle interface checks. The selector denotes the anchor's
logical data, with no role-local component and no executable extraction.
Ordinary data, handle sequences, unknown directions and out-of-range ports
refuse; an anchor cannot be a Boolean decision. A selected `protocol.statement`
may retain the logical relation with actual entry anchor operands. Such operands
use the string selector `anchor` and require an exact owned `target` clause.
The relation signature is checked against their kind-associated Data types;
ordinary operands keep their role selectors. The operand type distinguishes
an anchor marker from a participant name. A standalone unowned statement cannot
introduce this logical interpretation. Checked realization must replace the
logical binding before ordinary statement projection or executable export.

### Virtual query declarations

`protocol.oracle` is a closed symbol with a single query region. Its function
signature lists source handles first, ordinary parameters next, and the queried
position last; its one result is the declared kind's answer. The body contains
ordered source queries, closed total Math helpers and primitives, and one
`oracle_yield`. Query owners are implicit inside this region and explicit in a
protocol. Query sites remain distinct, including repeated or unused reads.

Every query uses a declared source handle. Its position may depend on the queried
position and ordinary parameters, but never on an earlier answer. The dependency
check uses the actual closed helper summaries, so a helper cannot hide an adaptive
query. Polynomial observations also check their actual degree bounds on a bounded
private expansion, before unused work can be removed. All retained declarations,
including unused ones, share the common admission allowance.

The declaration names an admissibility predicate over source data and ordinary
parameters. Each `oracle_virtual` occurrence instantiates that obligation using
its actual anchors and parameters. Retaining the predicate is not proving it;
source/export and the independent bridge must carry this obligation explicitly.
The predicate covers the domain and shape assumptions needed for its query maps
and pointwise holder data. It does not authorize sampling, stops or execution in
the mathematical answer body.

The kind owns named dimensions and optional static extents. Every dynamic
dimension appears once in `shape_arguments`, mapping its name to an ordinary
index parameter, and once in `shape_bounds`, mapping it to an unsigned maximum.
Static dimensions appear in neither map. A source handle or the query parameter
cannot supply a shape argument. Each construction checks that every selected
parameter is initially bound under the common shape policy. Shape/data
consistency and each maximum still need realization checks before publication.

`oracle_virtual` requires its sources and parameters at the holder and every
receiver; the holder must hold each source's data. It allocates a fresh occurrence
anchor, without an observed query event. Ordered allocation effects prevent CSE
from merging equal constructions. Its actual closed declaration remains unchanged
through preparation and is compared independently together with its retained
helper/domain closure and actual admissibility declaration. A matching symbol
name does not justify a substituted body or predicate. Queries on a dynamically selected virtual handle
must later expand using that runtime anchor, not a static possible-origin list.

### Oracle observation scheduling

The compiler's scheduling analysis reads one selected observer of an admitted,
prepared protocol. Applications must already be expanded, including their role
substitution. It reports whether some considered execution prefix contains an
oracle query followed by a challenge draw. The summary composes normally
continuing paths separately from stopped paths. A guard or early completion at
another participant never ends the selected observer's flow.

Known loop counts use exact repetition; unknown counts include every count up
to the checked maximum and a possible bound failure. Constant invariant captures
can be followed through repeats. Induction and carried arguments remain unknown,
even when their initial values are constants. Fallible local work may stop or
continue. These choices overapproximate the selected observer's paths and can
refuse an otherwise valid final-draw policy. Work and nesting have explicit
analysis limits. The analysis neither changes the protocol nor authorizes
batching, authentication, query-domain assumptions or a realization simulation.

## Total mathematics and helpers

The [structured extension](mathematics.md) adds field constants and
subtraction, static field arrays and formal polynomial operations. It owns their
exact types, degree checks and realization.


The scalar total vocabulary is field addition, multiplication and equality; group
identity, addition, scalar action and equality; ordered bilinear pairing into its
declared target group; and the following closed subset of MLIR
`arith`. Domains are installed logical identities. Scalar action uses the
group's associated scalar field, including zero and group identity.

| Operation | Admitted form |
|---|---|
| `arith.constant` | Scalar `i1` Boolean literal |
| `arith.andi`, `arith.ori`, `arith.xori` | Scalar `i1` operands and result |
| `arith.cmpi` | Scalar `i1`, predicates `eq` and `ne` only |
| `arith.select` | Scalar `i1` condition and matching Boolean, field or group arms |

Registered external interfaces describe the upstream operations. Closed
admission independently checks exact identities, attributes, types and complete
operand dependencies in operand order, exactly once each. This closed profile
clones whole operations; a partial or reordered dependency list is refused.
Missing or malformed models, other integer widths,
vectors, arbitrary predicates, poison/undef and other operations are refused
before optimization, even when unused. This is not a dialect-wide permission.

Algebra operation formation is independent of the enclosing protocol and any
execution implementation. The domain verifier checks nominal field/group
identity, matching operands/results and the group's associated scalar field
against the installed domain catalog. The same operation can appear in a
standalone function. Protocol admission separately restricts its contexts,
availability and admitted helper bodies; lowering separately selects a recipe
and diagnoses a missing execution implementation.

These operations are total, deterministic, copyable and discardable on their
logical domains. They are represented by dedicated registered operations with
MLIR's `Pure` trait. Purity is a positive interpretation of this vocabulary;
an empty effect list or an installed kernel signature alone cannot establish it.
Bound kernel operations have their own effects and possible
stops. Partial arithmetic, resources and unknown operations are outside this
total vocabulary.

`arith.select(c, a, b)` depends on all three operands, including `c`.
All are total values; this operation neither represents distributed control
nor short-circuits an ordered action. A private condition cannot select a
shared result merely because both arms are shared.

Private, defined `func.func` helpers contain only this total vocabulary and
calls to other admitted helpers. Their bodies are acyclic and single-block.
The compiler derives each result's dependencies from the current body. Helpers
contain no role selectors, statements, communication or stopping. The same
helper can therefore be used under different role rosters. Admission checks
every definition, including unreferenced helpers, before optimization. After
that check, an unreferenced private definition may be discarded. Per-result
summaries also retain availability requirements from unused intermediate
expressions; removing an unused result cannot excuse an unavailable original
computation. Selected
implementation work/depth bounds may refuse an otherwise valid acyclic helper
graph; such refusal is not an assertion that the mathematical program is
invalid. [Static protocol applications](composition.md) have a separate
role substitution and effect contract; they are not pure helper calls.

## Executable local calls and type use

A private `func.func` with plain mathematical ports is transparent total
computation. A scoped function with an explicit scope input and outcome result
is ordered execution that may stop, consume capabilities or fail under work
and storage limits; its actual CFG is checked by the
[scoped execution profile](execution.md#source-scoped-helper-profile).
`protocol.local_call` invokes one such
function at one owner, with exact available operands and owner-only results on
normal return. Projection retains `protocol.local_call` at that owner's
participant and checks its role against the enclosing participant. This action
owns the runtime invocation boundary; an ordinary scoped `func.call` inside a
helper instead borrows the active scope. Calls
remain observable work even with unused or zero results. They are not pure,
inlined as mathematical helpers, merged, or moved across action cuts.
Preparation and projection retain every immediate function and domain
definition, including dormant ones. The preservation checker compares actual
bodies, attributes and bindings, independently of the participant call list.
Plain mathematical definitions can be consumed later by the checked numerical
realization boundary; scoped execution cannot be silently erased there.

Scoped source execution invokes total mathematics through `exec.compute`, with
an owned [numerical unit](computation.md). Its helper is defined, acyclic and admitted
by the whole-module mathematical checker. Only executable data crosses the call
boundary; formal polynomials and capabilities remain inside their owning
abstractions. The complete helper/domain closure and actual call data flow are
checked against the original source and frozen through preparation and
projection. Numerical selection occurs after demand placement. Relation formulas
remain specification-only declarations.

Numerical realization uses checked helper normalization, polynomial observation
checks and execution recipes under bounded work. An independent read-only
normalization checker interprets calls by positional substitution and checks
polynomial meaning, static shape facts and every result coordinate. It checks
unused observations before accepting their removal. Cached normalization does
not refund the work charged for each emitted occurrence.

The mathematical recipe matcher then compares the checked expressions,
operands and returns against the generated local body. A separate structural
containment check preserves unrelated declarations and the realization's exact
signature and origin. It admits only the closed calculation recipe vocabulary,
excludes capabilities, history, sampling, unrelated partial contracts and explicit
stops, and accounts for added bindings. Membership in that vocabulary alone does
not ensure total execution: for example, vector-to-array conversion also needs an
exact length. The recipe matcher checks those constructed instances. This is
bounded native correspondence checking over the supported vocabulary, not a
formal proof of arbitrary helper equivalence or native runtime semantics.
Resource exhaustion remains a possible runtime failure, as
with other realized total calculations.

### Checked pointwise maps

A pointwise map uses the general [scoped collection request](execution.md#ordered-finite-requests).
A private `data.domain` reads the marked vector arguments and combines their
elements with strict zip. Its private scoped callback takes the current items
and the complete original captures, then invokes the scalar mathematics through
`exec.compute`. The outer request has the form:

```mlir
%attempt = "exec.collect"(%scope, %rows, %scalar)
  {domain=@items, body=@row, site="map"}
  : (!runtime.scope, !V, !F) -> !exec.outcome<(!V)>
```

The surrounding function dispatches the outcome before using its vector payload.
There is no separate map-declaration or row-mask owner in this source path.
The [source `map` syntax](../language/definitions.md#checked-pointwise-maps)
requires one installed field across the scalar helper's input and result ports,
at least one marked vector and exact argument binding. General collection IR
admits other typed domains and callbacks; the source syntax's field restriction
is not a restriction on that IR.

Formation reads the complete actual domain and callback signatures. Every
retained `exec.compute` request admits its mathematical helper closure, including
unused operations, under the shared mathematical analysis bounds. Typed
mathematics outside the field-ring fragment is permitted. Ring extraction is an
optional bulk optimization, and its depth or expression capacity does not
invalidate an otherwise admitted callback.

Preparation retains an immutable source subject until its candidate passes
independent checking. Complete domain admission precedes every callback or bulk
payload. For the strict-zip map domain, all vector lengths are measured in input
order, followed by equality checks against the first length and ordered
`control.require` calls. Unused columns retain their checks. A shape mismatch is
`rejected:require`; an unused map result still checks shapes. Argument evaluation
and surrounding ordered operations retain their original positions.

Selection can use:

- A [native expression call](../runtime/numerical.md#pointwise-expressions),
  borrowing exact typed columns and scalar captures and constructing one output.
- A vector realization using installed `field.*`, `vector.add/sub/mul/scale` and
  `vector.fill` operations. Scalar subexpressions are evaluated once and
  admitted equal subexpressions may share storage.
- Required ordered collection, invoking the actual scoped callback for each row,
  when optional recognition, construction or comparison cannot select a bulk form.

An admitted identity formula can return its original column after the complete
guard prefix. Empty aligned inputs succeed. Formula extraction admits all
reached mathematics before omitting unused total arithmetic; it cannot remove or
move an ordered guard. Optional work is shared across occurrences and retries.
Its exhaustion cannot spend or reset the separate required construction and
checking reserves. Required capacity refuses publication without changing the
source. Retained and generated callbacks both count toward actual candidate
admission; source admission alone does not promise that every candidate fits.

The independent reader interprets the original domain and callback against the
actual scoped candidate. It checks nominal fields, literals, scalar/row positions,
expression bodies, broadcasts, guards, sites, result uses, retained declarations
and surrounding code. Producer classifications or emission plans supply no
checking evidence. The relation covers equal values and ordered shape refusals
under sufficient resources; allocation charges and exact exhaustion may differ.
Occurrence names follow the input-relative scoped helper convention
in [execution IR](execution.md). Executable publication refuses unresolved
collection and computation requests, including dormant ones.

### Optional vector reduction fusion

`--fuse-vector-reductions` defaults to false, independently of finite bulk
selection, simplification and storage release. The same
`MathematicalSelectionPolicy` is carried through preparation and projection to
late realization. Retaining a map does not itself authorize fusion.

An eligible pair is a scoped `exec.collect` followed by an `exec.apply` of the
native `vector.sum` contract, with the collected vector used only by that sum.
Adjacency is in the admitted ordered execution steps: the required outcome
dispatch blocks are administrative control flow. The exact field identity and
empty parameter list must agree, and neither an explicit binding selection nor
a fixed reducer implementation permits replacement. Late selection can use:

- `vector.dot` when the admitted live formula is exactly the product of two
  row slots, including equal slots;
- `numerical.sum` for a supported pointwise field formula;
- a native or vector map followed by the original sum if fusion is unavailable
  and finite bulk selection is enabled;
- ordered collection followed by the original sum as the required endpoint.

The fusion policy independently permits the dot and summed-expression choices.
It does not enable ordinary bulk collection lowering. An unavailable provider
advances only the implicated occurrence through its permitted alternatives.
Discarded construction and optional recognition/comparison work stay charged.

Every choice preserves the complete original ordered shape-check prefix,
including unused rows, and the surrounding argument evaluations. Fixed bindings,
custom reducers, intervening effects, regions and escaping map results do not
acquire replacement permission. Other reducers retain their original calls.

The [checked physical plan](../../compiler/representation.md#checked-physical-decisions)
selects feasible alternatives per occurrence before publication. Its independent
reader interprets the original domain and callback against the actual selected
scoped body, without accepting the producer's equation or recipe as evidence.
It checks all domain admission before comparing the scalar sum and preserves
the final reducer's occurrence and source location. Physical ports, implementations, conversions and final program capacity are
checked separately. A reached runtime failure never triggers another realization.

### Admitted type uses

The initial type-use policy is closed:

| Logical types | Native mathematical use |
|---|---|
| Boolean, field, group | Total operations, helpers, relation ports and role-family data |
| Static field arrays, including empty data | Selected total operations/helpers, shared ports and native array messages |
| Formal polynomial SSA | Selected total operations and transparent helpers; no runtime ABI or protocol boundary |
| Index/indices, vector/matrix, groups | Selected total data operations/helpers and shared ports; native wire admission remains separate |
| Polynomial/table/point/round, commitment(s), proof | Shared pass-through ports and local calls; codec permission checked separately |
| Opening state(s), prover/verifier keys | One-owner immutable custody through ports and local calls |
| Fixed vectors | One-owner aggregate custody, recursively checked element types; protocol ports recursively check payload custody |
| Variants | Copyable products/sums use total data operations and shared ports; affine variants remain local |
| RNG, nonce, transcript, resource unit | One-owner affine custody through ports and local calls |
| Service reference | One-owner entry, immutable iteration capture and direct query |

All type instances require their exact logical declarations. Sharing, totality,
wire permission, affine custody and installed representation are separate checks.
[Structured values and iteration](iteration.md) owns nominal collection
mapping, aggregate policy and loop invariants. Unknown families are refused.
Affine uses retain existing consumption/return and cleanup rules. Unreturned
logical resource units retire with their frame; completed cryptographic transitions
and service state persist. An exchange additionally requires shared permission
and an installed codec. The policy applies in all four native profiles; it is
not an author-supplied permission attribute.

## Ordered behavior

| Operation | Open participant interpretation |
|---|---|
| `protocol.exchange v` from A to B | A sends its component of `v`; B awaits an actual environment reply of that logical type |
| Exchange result | Available at A and B; aliases `v` at A and denotes the fresh received value at B |
| `protocol.local_call f(args)` owned by A | A executes the closed local function at this occurrence; other roles skip it |
| `protocol.guard c` owned by A | A continues on true and stops with `reject` on false; other roles skip it |
| `protocol.return` | Each role returns only its declared result components |

Senders and receivers are distinct declared roles. The sender must have the
sent component. A guard's owner must have its Boolean component. Every ordered
occurrence has a unique site within the common program. Ordered operations have
conservative read/write effects on the same default MLIR resource. Equal-looking
messages remain distinct receives, even when their sent operands are equal.

A failed guard does not broadcast failure. Another role may return or remain
pending at a later receive. A false returned acceptance Boolean also does not
stop earlier: subsequent ordered work still happens before the return.

## Statements and retention

Original declarations own source contracts. `relation.declare` optionally has
a flat symbol reference `formula`; the kind `zkc.language.formula/0` requires it
in the `protocol` profile. It resolves in the same unit to a defined Math
`func.func` with exactly the declaration's complete input/output ABI. Other
kinds have no formula link. A scoped executable helper is not total Math, and a generated symbol
spelling is not a binding rule. Ordinary MLIR symbol replacement updates these
references. This is a structural association, not a proof of the formula's
adequacy or totality.

`protocol.func` optionally has `contracts`, an array of declaration clauses;
absence denotes an empty inventory. Each clause has exactly five fields:
`[kind, name, subject, residual, decision]`. Applications are
`[@relation, [selectors...]]`, selectors are
`["input" | "output", native-port-index : i64, "role"]`, and absent residuals
or decisions are `unit`. Kinds, directions, exact native ABI, owner roles,
unique names and clause-specific residual/decision rules follow the
[structured contract layout](../formats/structured-source.md). A declaration
admits at most 4096 clauses and 100000 units of application, selector and entry
agreement work. Invalid contracts use `protocol-contract`; disagreement with an
entry statement uses `protocol-contract-statement`. Invalid formula links use
`relation-formula`. These checks also apply to hand-authored original PIR. The same owner supplies
a typed contract inventory to downstream readers: component selectors retain
role, direction, port and type; anchor selectors retain direction, port and kind.
Continuation residuals and exact named statement selections remain distinct.
This view borrows the original context, is invalid after mutation, and does not
admit the remaining program or interpret external predicates.

Contracts do not add statement operations, guards or witness equalities.
Application expansion retains the declaration inventory and its symbol
references; it does not attach callee entry indices to caller instructions.
Participant projection deliberately erases declaration contracts and formula
links, and the statement's selected-target reference. The artifact retains
helper bodies and domains for execution preparation, but does not retain the
original protocol contract subject. It retains the existing statement
identity/ABI projection. No certificate for the
original contracts is transported through these transforms by this metadata.

`protocol.statement` references a non-callable `relation.declare` symbol and
binds ordered entry operands with explicit role selectors or the checked
logical anchor selectors defined above. The declaration has
an external identity `(kind, key, revision, static_arguments)`, ordered logical
input types, one Boolean result, and an explicit purpose for every input: `parameter`,
`statement`, or `witness`. Purpose comes from an author or adapter schema; role
availability and secrecy do not determine it. The symbol implements no callable
interface and cannot be invoked as a helper or executable local function.

`static_arguments` is an ordered ArrayAttr of canonical typed static trees,
using the protocol-origin serializer and checker. Its native default is empty;
the structured wire row always contains the list. Arguments are retained even
when unused by runtime input types. The origin limits apply: at most 128
arguments, depth 64 and 4096 aggregate term nodes. Noncanonical naturals and
malformed typed trees refuse with `relation-static-arguments`. Source-owned
`zkc.` formula and captured-asset identities require an empty list and retain
their exact helper or asset identity. Vendor families obtain meaning only from
an explicit registry with a fixed typed instantiation and exact ABI/purposes.

The statement's optional StringAttr `target` names exactly one `target` clause
in the containing protocol's `contracts`. Its relation, actual input arguments,
input roles and acceptance index must match that clause; the clause recovers the
selected decision role. The reference cannot resolve in another protocol.
Source proof Entry emission always retains its selected target name, and source
interface admission checks that name together with the verifier/decision-role
agreement. Native proof deployment additionally checks the recovered decision
role against its validator. Hand-authored standalone statements can omit the
reference; with retained targets they still require some matching projection,
but supply no exact selected-target evidence. Changing the selected name to
another well-formed target represents a different selection even when the old
projection fields are identical. The reference is metadata, not a predicate call.

Declaration inputs admit immutable logical data: Boolean and unsigned index
scalars, installed field/group scalars, static one-dimensional field arrays,
dynamic field vectors/matrices, group/index vectors, and recursively nested
copyable sequences and nominal variants over this vocabulary. A record is a
single-alternative variant. All alternatives must satisfy the data rule, including
inactive alternatives. Keys, service references, affine resources, mutable
storage, physical wrappers and owner-local `fixed_vector` values are excluded.
Copyability alone does not confer relation-data permission. An oracle handle
is never a relation formal: its anchor selector binds the associated Data type.
Polynomial objects and cryptographic commitment/proof objects require their own
relation interface extension.

The complete canonical logical type is part of declaration consistency:
element domain, rank, static extent, sequence element and nominal alternative
names and ordered payloads. Dynamic dimensions are value properties; a declaration
does not equate matrix dimensions or prove bounds for indexing. Such conditions
need explicit executable checks or separately justified contracts. Builtin MLIR
tensors have no logical collection encoding or compatibility alias in this profile.

A purpose applies to its entire input, including nested leaves. Mixed purposes
use separate entry ports. No per-member selector, computed operand or flattening
is inferred. Declaration admission is independent of executable host construction
and wire-codec availability. Native formation bounds a signature to 100000
inputs, 200000 expanded structural nodes, structural depth below 64 and 64 MiB
of expanded string metadata. These limits are shared across all inputs; repeated
occurrences of a uniqued type still count. Native consistency compares formed
constructors, typed arguments, complete identity trees and ordered alternatives
directly, including across MLIR contexts. It does not serialize a type or depend
on the byte grammar's depth or spelling limits. Publication separately checks
the selected external format and can refuse an otherwise formed native type.
Budget exhaustion uses `relation-declaration-signature`.

Declarations with the same external identity must agree on input types and
purposes within a unit and across the units explicitly selected into one
compilation or linked bundle. Current commands check one unit; the public C++
consistency API also compares explicitly supplied units across MLIR contexts.
This API does not perform linking. Unrelated invocations do not share a global
registry. The identity names a supplied relation contract; it neither defines
that predicate nor proves provider conformance or satisfaction. Existing
R1CS/AIR assets retain their declared interfaces without inferred purpose
mappings. The statement designates a Boolean common result as its acceptance
port.
That port has its own declared role set; each witness-binding role need not
also receive the verifier's acceptance result. Each exposed role observes its own
component. The components may differ, including when an exchange receiver is
supplied a different Boolean. Designating this result does not establish a
single global decision, agreement between roles, or a rule for aggregating
acceptance. A consumer must select the relevant role observation or provide
its own explicit aggregation contract.

Statement operands must be entry ports in this profile. A retained computed
expression or a composed statement needs a separate extension. Statements have
a retention effect, so ordinary DCE cannot remove them. They do not create
participant execution demand. Projection retains the original function type, input/result role sets,
per-role argument and service-port maps, relation signatures and external
identities, explicit purposes, selectors, acceptance indices, and ordered
source action occurrences in one `protocol.projection` operation directly
inside the generated `protocol.module` symbol table. Relation, participant, entry
and generated-callee references are actual MLIR symbol references. Symbol
renaming updates them and the operation keeps private referenced declarations
live through symbol DCE.

An acceptance index identifies the original common result. The retained
per-role result maps identify each corresponding participant result. Service input
indices identify original common ports; the participant's service port table uses
its own combined data/service ingress indices. Structural verification checks
both mappings against the original interface and actual participant signature.
At the physical stage, it compares original logical types with the logical
component of admitted physical wrappers; independent representation checks
still apply.

`participant` requires exactly one projection record. `exec` and `physical`
profiles validate a record when present. A compiler pass also compares its
candidate against its frozen input, so deleting the record cannot turn a
projected result into an unrelated supplied program. Generated calculation
origins distinguish generated calculation sites from retained source action occurrences.
Retained interfaces are immutable through lowering and physical selection. A
guard's retained target remains `protocol.guard`, describing the original projection.
Projection retains its `owner`, which must match the selected participant role.
The checked profile derives whether its current implementation must be that guard
or a generated `protocol.local_call`; lowering does not rewrite source facts. Only the
separate generated-calculation list is added during lowering.

The enclosing protocol module owns full metadata/profile verification. The
projection operation's symbol-user interface checks reference resolution and
retains normal rename/DCE behavior. One bounded type-policy cache is shared
within each full module check; a later verification recomputes it. Direct public
profile-verification helpers still validate metadata. The record has a retention
effect and produces no participant runtime event.

The original common module and candidate remain distinct artifacts when
assessing preservation. This metadata is a checked compiler view, not an
independent correspondence or security certificate. Participant JSON export
does not add these fields; importing a supplied carrier does not invent them.

## Projection and realization boundary

Preparation validates the original unit, expands admitted pure helpers on a
candidate copy, and runs canonicalization/CSE inside mathematical bodies. The
selected patterns and explicit greedy worklist contain only admitted total
operations present in those bodies, with `ExistingOps` strictness. Non-total fold
hooks are excluded. Standard MLIR CSE follows, after checking that only total
operations, admitted role restrictions and terminators can be effect-free.
Other actions must have a write effect or conservatively unknown effects. Ordered action
identity and attributes must survive both steps. Resulting IR must still pass
closed admission. Executable local bodies are outside that optimization scope.

`zkc-project-protocol` produces `participant`. It clones demanded total
expressions into each role, preserves all advertised ports, and creates
`protocol.send`, `protocol.receive`, service queries, authored `protocol.local_call`, and `protocol.guard`
occurrences. It creates no new executable calculation functions or bindings.
Receive results are actual environment replies. The sender's exchange result
aliases its sent component; that fact grants no equality at the receiver.

`zkc-simplify-participant` applies the selected total-operation patterns and
CSE only within participant bodies. It can share expressions that become equal
after role projection while preserving the original interface and ordered
actions. Every resulting candidate must pass closed admission and the frozen
interface postcondition.

`zkc-lower-closed-participant` closes a participant deployment before
forming its mathematical computations. It applies independently checked scoped helper
substitution, then removes scoped helper definitions unreachable from the
participant context, using MLIR symbol references. Every other declaration is
a live root, including all entries, participants, bindings, mathematical definitions,
relations and projection metadata. The independent pruning checker admits both
actual modules and requires the candidate to be an unchanged, ordered
subsequence of the source declarations, with only scoped definitions omitted.
Candidate admission rules out any retained reference to an omitted definition.
Invalid dormant helpers therefore cannot escape source admission. This edge
applies only to the participant profile; it cannot remove role-free exported
functions. Pruning does not change any executed operation or resource charge.
Native compilation and the full textual participant pipeline run this pass.
It composes the separately checked expansion, pruning and computation-formation
edges, expanding helpers only once before pruning. Standalone mathematical lowering retains every authored
definition; it does not treat its input as a closed deployment.

`zkc-lower-math` applies independently checked scoped helper substitution and
produces `exec` with retained mathematical computation units. For every local
action or finish cut, it finds total dependencies not previously computed and
schedules them in dependency order with source-order tie breaking. Work starts
at its first consumer, so an earlier guard cannot trigger unrelated later
calculations. A value needed at several cuts is computed once and passed as a
participant SSA result to later calls. Each generated scoped `func.func` has one
`protocol.local_call` invocation and exposes only total mathematical data at that
participant boundary. Unused result ports are removed after
original participant expressions have been erased; this does not remove executable
work inside the generated function. A guard ends its calculation segment
with `exec.test` and checked Func/CF branches: true continues through a charged
`exec.complete`; false executes `exec.reject` with explicit reason `reject`.
The scoped function may have an empty outcome payload.
The false arm stops that participant before its next action. A failure to read the
Boolean representation remains a backend failure.

The existing bound `control.require` operation is not this recipe: its installed
backend reports `rejected:require` as a backend failure. Reclassifying that error
would change an existing observable contract. Authored bound uses retain their
outcomes and accounting.

Lowering disables implicit dialect-conversion folding. Total simplification is
an explicit earlier stage; executable recipes have deterministic sites and
retain the selected instruction structure. XOR and comparison use existing
Boolean kernels. Selection of Boolean, index, field and group scalars uses
the corresponding deterministic `*.select` contract on already evaluated
operands. A literal uses the [native participant instruction](../formats/program.md).

Each total calculation becomes an owned numerical entry invoked by typed
`exec.compute` from its scoped wrapper. The guard remains outside that unit.
Root packaging uses `exec.returned`; native participant completion belongs to
the subsequent checked executable realization. All original mathematical,
scoped and domain definitions survive this preparation edge. Verification
checks the logical candidate before publication. Numerical realization must
consume every request before physical publication; the current migration
coverage is recorded in [implementation status](../../status.md).

The Transforms component then compares the verified `exec` candidate against its
frozen `participant` input. This closed postcondition independently walks source
dependencies at each first demand and matches the actual numerical body in source
order. Numerical realization separately checks the generated executable recipes. It checks exact resolved contracts and their domain arguments, captures,
returned values, guard conditions and rejection, and ordered action operands.
Entry arguments and actual receive/call/query results are distinct SSA anchors.
Every generated calculation is a fresh symbol with one invocation and its own
logical origin. Only these functions, their closed control bodies, their numerical
units and accounted recipe bindings may be
added to the frozen symbol table. Extra work, recomputation and
work moved across an earlier cut refuse. The traversal uses explicit worklists
and a shared limit of one million operation/operand comparison units for the
module pair. An otherwise admitted program may exceed this separate compilation
budget and be refused with `mathematical-lowering-preservation`; admission does
not guarantee that every transformation fits its work budget. It does not recursively expand SSA chains or generated calls.

This comparison checks the compiler's specified schedule and recipes, rather
than accepting arbitrary equivalent executable programs. Protocol-to-participant
projection and mathematical simplification still rely on their implementations,
MLIR rewrites and their own structural checks; the lowering postcondition does not
provide independent Structured source correspondence or prove backend primitives. Projection, simplification, lowering, and physical selection
preserve the retained interfaces and statement bindings.

The projection-preservation API compares protocol-to-participant,
participant-to-exec, exec-to-physical, or same-profile participant/exec/physical
subjects. Skipped and backward edges refuse with `mathematical-projection`;
protocol preparation has its own check. An admitted edge does not expand the
check's evidence scope. Executable subjects without projection metadata still
receive the participant count and logical-body comparison. This adjacent check
adds no Structured source correspondence to their separate admission contract.

Every math lowering result selects the native participant execution
contract, with physical-only external export. The realization uses the existing
logical bindings and physical planner.
Generated local functions are logical definitions with their own identities;
their `logical_origin` is not a proof of correspondence to the common source.
Physical backend admission, work limits, representation capacity and host
failures remain realization obligations. They are not mathematical branches or
permission to mark bound kernels pure. Source totality alone does not
establish unconditional equality to a resource-bounded physical execution.

Open replies here are typed logical values. A payload-only FIFO network,
administrative label interpretation, joint scheduling and timeout classification
need a separately selected driver contract. The [native service extension](../runtime/services.md) adds explicit queries and
registry-managed root aliases. An affine RNG token is not such a reference
merely because its value was copied.

The supplied native participant carrier can be independently admitted and
executed without a source correspondence claim. A Lean interpretation and
correspondence for this native profile remain open. Independently formalized
source models have their own subjects and admission contracts.

## Conditional completion extension

The native mathematical path also supports [conditional entry completion and
bounded local termination](completion.md). Its records belong to the native executable; independent formal models require
their own explicit interpretation.

## Retained frontend declarations

An original protocol module may carry the `source_declarations` string
attribute specified by the [structured export](../formats/structured-source.md#retained-source-declarations).
It retains checked closed source records and protocol port boundaries for
component association. It has no execution meaning, is checked exactly by
frontend correspondence, and is omitted by participant projection. Contracts
and component routes remain original-stage facts; no second identity digest
or executable routing table is introduced.
