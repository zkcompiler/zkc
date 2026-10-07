# Closed mathematical protocols

This profile defines a closed, straight-line common protocol containing total
mathematics, messages, owner-local executable calls, immediate guards and a
retained statement interface.
Its meaning is a family of open participant behaviors. It uses
[interaction and endpoints](../../language/interaction.md),
[relations and terminals](../../properties/relations.md) and the
[realization requirements](../../realization/representations.md).
Implementation coverage and deferred connections belong to [status](../../../status.md).

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

Mathematical operations use ordinary logical types and SSA edges. Interface
attributes and explicit `protocol.restrict_roles` operations retain declared role
boundaries. Intermediate availability is derived, never supplied as a trusted
summary. A total operation's availability is the intersection of its operand
availability; an operation with no dependencies would be available at every
declared role. A restriction selects a nonempty subset of an existing value's
components. It neither communicates nor changes their values.

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
explained in [the rationale](../../../rationale/flat-mathematical-ssa.md).
No intermediate located common program is required by this profile.

## Total mathematics and helpers

The [structured extension](structured-mathematics.md) adds field constants and
subtraction, static field arrays and formal polynomial operations. It owns their
exact types, degree checks and realization.


The scalar total vocabulary is field addition, multiplication and equality; group
addition, scalar action and equality; ordered bilinear pairing into its declared
target group; and the following closed subset of MLIR
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
The transitional `protocol.math_and` and `protocol.select_value` operations are
removed; use `arith.andi` and `arith.select`.

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
The older bound kernel operations keep their separate effects and possible
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
invalid. [Static protocol applications](protocol-composition.md) have a separate
role substitution and effect contract; they are not pure helper calls.

## Executable local calls and type use

A private `func.func` helper is transparent total computation. An executable
`local.func` is an ordered local program that may stop, consume capabilities or
fail under work and storage limits. `protocol.local_call` invokes one such
function at one owner, with exact available operands and owner-only results on
normal return. It projects to a role-free `local.call` at that owner. Calls
remain observable work even with unused or zero results. They are not pure,
inlined as mathematical helpers, merged, or moved across action cuts.

The protocol profile can declare an executable realization of a total helper:

```mlir
local.realize @evaluate = @mathematical_helper : (T...) -> (U...)
```

The helper is private, defined, acyclic and admitted by the same whole-module
mathematical checker. Its exact signature must contain only executable total
data; formal polynomials and capabilities cannot cross this boundary. A local
body invokes the declaration with `local.apply`. The declaration is a preparation
request, carries no body or runtime provider, and is forbidden in participant
and executable profiles. Ordinary portable source admission has no external
signature permission for such an application.

Preparation expands pure helpers into the requested realization, checks every
polynomial observation before dead-expression elimination, then reuses polynomial
elimination and mathematical execution recipes. The resulting `local.func` keeps
the realization symbol and signature, and its logical origin names the pure
helper. Admission conservatively bounds expanded helper operations across all
realizations, including helper call and return overhead.
Polynomial expansion and final executable instruction limits are checked during
preparation; an admitted declaration can still exceed these realization limits.
After polynomial checks and elimination, static dimension queries become index
constants and unused total expressions are removed before becoming ordered
execution. This normalization applies to helper realization.

The independent mathematical recipe matcher compares the remaining expressions,
operands and returns against the generated local body. A separate structural
containment check preserves unrelated declarations and the realization's exact
signature and origin. It admits only the closed calculation recipe vocabulary,
excludes capabilities, history, sampling, unrelated partial contracts and explicit
stops, and accounts for added bindings. Membership in that vocabulary alone does
not ensure total execution: for example, vector-to-array conversion also needs an
exact length. The recipe matcher checks those constructed instances. Helper
expansion, static shape normalization and polynomial elimination remain trusted
on this edge; these checks are not an independent proof of their
arithmetic semantics. Resource exhaustion remains a possible runtime failure, as
with other realized total calculations.

Preparation then expands admitted `local.apply` using `canonical-expanded-locals/1`
before freezing local definitions. An application inside a local region remains
inside that region; it is not hoisted to protocol mathematics. Subsequent common preparation,
projection, participant simplification and lowering preserve those bodies and their
binding declarations. Physical selection may change representations and insert
checked storage releases under the selected execution contract. An authored
partial inverse stays in a local function; a preceding mathematical guard does
not make inversion a total operation.

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
[Structured values and iteration](structured-iteration.md) owns canonical tensor
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

`protocol.statement` references a non-callable `relation.declare` symbol and
binds ordered entry operands with explicit role selectors. The declaration has
an external identity `(kind, key, revision)`, ordered logical input types, one
Boolean result, and an explicit purpose for every input: `parameter`,
`statement`, or `witness`. Purpose comes from an author or adapter schema; role
availability and secrecy do not determine it. The symbol implements no callable
interface and cannot be invoked as a helper or executable local function.

Declaration inputs admit immutable logical data: Boolean and unsigned index
scalars, installed field/group scalars, static one-dimensional field arrays,
dynamic field vectors/matrices, group/index vectors, and recursively nested
copyable sequences and nominal variants over this vocabulary. A record is a
single-alternative variant. All alternatives must satisfy the data rule, including
inactive alternatives. Keys, service references, affine resources, mutable
storage, physical wrappers and owner-local `fixed_vector` values are excluded.
Copyability alone does not confer relation-data permission. Polynomial/oracle
objects and cryptographic commitment/proof objects require their own relation
interface extension.

The complete canonical logical type is part of declaration consistency:
element domain, rank, static extent, sequence element and nominal alternative
names and ordered payloads. Dynamic dimensions are value properties; a declaration
does not equate matrix dimensions or prove bounds for indexing. Such conditions
need explicit executable checks or separately justified contracts. Static rank-two
MLIR tensors have no canonical logical matrix encoding in this profile.

A purpose applies to its entire input, including nested leaves. Mixed purposes
use separate entry ports. No per-member selector, computed operand or flattening
is inferred. Declaration admission is independent of executable host construction
and wire-codec availability. The implementation bounds a signature to 100000
inputs, 1 MiB of total canonical type spellings and a shared 200000-unit type
traversal budget with nesting depth 64; the logical parser and nominal-descriptor
limits also apply. Budget exhaustion uses `relation-declaration-signature`.

Declarations with the same external identity must agree on input types and
purposes within a unit and across the units explicitly selected into one
compilation or linked bundle. Current commands check one unit; the public C++
consistency API also compares explicitly supplied units across MLIR contexts.
This API does not perform linking. Unrelated invocations do not share a global
registry. The identity names a supplied relation contract; it neither defines
that predicate nor proves provider conformance or satisfaction. Existing
`protocol_exec` R1CS/AIR assets keep their own interfaces without invented purpose
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
guard's retained target remains `local.guard`, describing the original projection.
The checked profile derives whether its current implementation must be that guard
or a generated `local.call`; lowering does not rewrite source facts. Only the
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
`protocol.send`, `protocol.receive`, service queries, authored `local.call`, and `local.guard`
occurrences. It creates no new executable calculation functions or bindings.
Receive results are actual environment replies. The sender's exchange result
aliases its sent component; that fact grants no equality at the receiver.

`zkc-simplify-participant` applies the selected total-operation patterns and
CSE only within participant bodies. It can share expressions that become equal
after role projection while preserving the original interface and ordered
actions. Every resulting candidate must pass closed admission and the frozen
interface postcondition.

`zkc-lower-math` separately produces `exec`. For every local
action or finish cut, it finds total dependencies not previously computed and
schedules them in dependency order with source-order tie breaking. Work starts
at its first consumer, so an earlier guard cannot trigger unrelated later
calculations. A value needed at several cuts is computed once and passed as an
participant SSA result to later calls. Each generated `local.func` has one invocation and takes and
returns only total mathematical data. Unused result ports are removed after
original participant expressions have been erased; this does not remove executable
work inside the generated function. A guard ends its calculation segment
with `local.if`: true continues through `local.yield`; false executes
`local.stop` with explicit reason `reject`. The function can have no results.
The false arm stops that participant before its next action. A failure to read the
Boolean representation remains a backend failure.

The existing bound `control.require` operation is not this recipe: its installed
backend reports `rejected:require` as a backend failure. Reclassifying that error
would change an existing observable contract. Authored bound uses retain their
outcomes and accounting.

Lowering disables implicit dialect-conversion folding. Total simplification is
an explicit earlier stage; executable recipes have deterministic sites and
retain the selected instruction structure. XOR and comparison use existing
Boolean kernels; selection uses local conditional control with already evaluated
data captures. A literal uses the separately versioned
[native participant instruction](program.md).

Full dialect conversion applies registered recipes only in generated local
functions and refuses any remaining total expression or guard there.
Verification checks the `exec` candidate before the pass publishes it.

The Transforms component then compares the verified `exec` candidate against its
frozen `participant` input. This closed postcondition independently walks source
dependencies at each first demand and matches the generated recipes in source
order. It checks exact resolved contracts and their domain arguments, captures,
returned values, guard conditions and rejection, and ordered action operands.
Entry arguments and actual receive/call/query results are distinct SSA anchors.
Every generated calculation is a fresh symbol with one invocation and its own
logical origin. Only these functions and their used binding declarations may be
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
provide independent common-source correspondence or prove backend primitives. Projection, simplification, lowering, and physical selection
preserve the retained interfaces and statement bindings.

The projection-preservation API compares protocol-to-participant,
participant-to-exec, exec-to-physical, or same-profile participant/exec/physical
subjects. Skipped and backward edges refuse with `mathematical-projection`;
protocol preparation has its own check. An admitted edge does not expand the
check's evidence scope. Executable subjects without projection metadata still
receive the participant count and logical-body comparison. This adjacent check
adds no common-source correspondence to their separate admission contract.

Every math lowering result selects the native participant execution
contract, with physical-only external export. The realization uses the existing
logical bindings and physical planner.
Generated local functions are logical definitions with their own identities;
their `logical_origin` is not a proof of correspondence to the common source.
Physical backend admission, work limits, representation capacity and host
failures remain realization obligations. They are not mathematical branches or
permission to mark old bound kernels pure. Source totality alone does not
establish unconditional equality to a resource-bounded physical execution.

Open replies here are typed logical values. A payload-only FIFO network,
administrative label interpretation, joint scheduling and timeout classification
need a separately selected driver contract. The [native service extension](native-services.md) adds explicit queries and
registry-managed root aliases. An affine RNG token is not such a reference
merely because its value was copied.

The native mathematical source is distinct from the existing source carrier.
Its supplied participant carrier can be independently admitted and executed
without a source correspondence claim. Lean implementation and checking for
this new common profile are deferred until the native core is stable; existing
Lean-backed source admission retains its existing contract.

## Conditional completion extension

The native mathematical path also supports [conditional entry completion and
bounded local termination](entry-completion.md). Its program-only records do
not extend the legacy carrier or its formal checker.
