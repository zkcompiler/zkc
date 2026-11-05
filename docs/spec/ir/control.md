# Structured local control

This compiler profile extends [local algorithms](functions.md) with
closed conditional, finite-variant match and finite-loop bodies. It applies inside scoped functions,
not protocol bodies. Language checks source captures and state results; native MLIR and executable
admission check their explicit representation.

## Formation

The portable records are:

```text
["if", site, condition, captures, then_body, else_body, outputs]
["for", site, induction, lower, upper, carried, captures, body, outputs]
["yield", values]
```

Each carried entry is `[region_argument, initial_outer_value]`. Every continuing
region has one final yield; an explicitly stopped region has no yield. A
continuing function has one final return. The program profile additionally admits
[bounded conditional termination](completion.md#bounded-local-termination)
through an explicit Boolean outcome payload and its `for_while` record. Local function early return,
unbounded loops and arbitrary jumps are not admitted. Sites are unique throughout
a function, including both arms and all nested regions. Regions obey the same
source size, depth and value limits as other local instructions.

An `if` condition has type `bool`. Each arm receives only the listed captures,
under their given names. Both arms must form, regardless of the runtime condition,
and yield the same ordered types. Capturing an affine value consumes its outer
binding once; each arm checks its own affine uses. Dropping a value is permitted
by affinity. An outer value needed after the branch must be returned through its
results rather than reused after consumption.

A `for` has two index operands in the same representation. Its body receives the
induction index, ordered carried arguments and explicitly listed invariant
captures. Invariant captures must be duplicable; affine state must use carried
ports. Yield types equal the initial carried types, and outputs have those same
types. No hidden access to the enclosing environment is admitted.

Finite local variants and exhaustive matches follow
[the variant carrier contract](variants.md). Their active payload
arguments are generated on region entry. Only captures are forwarded unchanged
along MLIR region successor edges; the scrutinee is not an operand of the
payload's type.

The compiler expresses these boundaries with standard Func/CF plus Exec and
Runtime operations. Closed region bodies are private `func.func` definitions
marked `runtime.region`; their arguments explicitly name induction, carried state
and captures. `exec.test`, `exec.range` and `exec.match` preserve reached admission
before CF chooses an edge. Scope entry, transfer and cleanup remain explicit.
Ordinary helper return packaging and charged region completion have distinct
operations. The [scoped instruction profile](execution.md#scoped-native-instruction-profile)
defines their exact forms; native records above are an independent carrier.

## Execution

`if` and `match` execute exactly one arm. Both branch typing and source/candidate
correspondence inspect both arms; runtime effects and failures come only from
the selected arm. Execution does not speculate a branch. A terminal stop
propagates out of every enclosing local region and function. No match dispatch
or continuation converts it into a recoverable result value.

`for` evaluates its lower and upper operands once and executes successive indices
in `[lower, upper)`, with unit increments. Upper at or below lower yields the
initial carried state without entering the body. Each completed iteration supplies
the next iteration's carried state. Failure stops immediately, preserving prior
observable effects. Each bound must be at most 1,048,576 in this executable
profile, including an inverted interval. This magnitude limit is deliberately
stronger than a trip-count limit and is not the mathematical meaning of index.

The native machine counts total entered iterations across protocol and local
loops and executed instructions against the Host's selected budgets: by default
100,000 iterations and 1,000,000 instructions, and at most 2^32 of each (see
[runtime capacity](../runtime/capacity.md#application-capacity)). Each executed
operation, conditional, loop, yield and return costs one instruction. Each entered
local region creates a backend child frame and charges its explicit inputs under
the [retained-value ledgers](../runtime/capacity.md#retained-values-and-logical-work):
inputs that share storage with their parent add none. A loop also charges its
induction index. The native runner validates every
backend-created induction value against the installed index representation
before entering the body. An untaken arm or zero-trip body creates
no frame. Region cleanup releases its retained charges, and returned values are
charged at the enclosing result bindings. Physical `release` has no instruction
cost and retains the ghost-accounting rule: released storage stays charged until
region cleanup, although a later allocation at a freed address is new storage.
These are retained-payload charges, not measurements of actual allocator memory
or constant-time execution.

Native local calls and nested regions use the same frame
lifecycle. A body stop remains primary when frame cleanup also fails; cleanup
errors are retained in the actual inner-to-outer order of frame exits. If the
body succeeds but its cleanup fails, the role stops with that backend error;
polling or retrying the consumed local cut cannot execute the body again. Completed
backend transitions are not rolled back by cleanup.

Bound rejection happens before the first body effect. Cumulative iteration or
instruction exhaustion may occur after earlier effects. Deterministic bound
rejection reports `exhausted:local-bound-limit`. Cumulative work exhaustion
retains its machine-limit cause. Comparisons preserve stop class, reached
prefix and resource state instead of identifying all failures with rejection.
Interpreter-work limits are separate.

Helper applications expand recursively before participant projection. Expansion
retains regions and does not unroll loops. Helpers introduce no runtime frames;
entered control regions do. Local origin paths append `["if", site, "then"]` or
`["if", site, "else"]`, and `["for", site, decimal_index]`, preserving the enclosing
call/participant origin. Source identities retain both branches and loop bodies,
including helper definitions reachable only inside a region.

## Analyses and construction

Analyses traverse every branch and retained body, while execution follows only
the chosen path. Exact resource-origin checks preserve actual affine successors
through control; unknown or conflicting origins refuse at the boundary that
requires them. See [resource origins](../../compiler/resource-origins.md).

Native transcript construction applies the selected
[proof policy](../formats/proof.md), including its loop, observation and state-chain
conditions. Local variant admission independently forbids specified history
operations inside matches. Neither structural control admission nor a local
Boolean result proves public transcript schedule safety.

Native proof construction, reverse request planning, native codec construction
and oracle realization require unconditional protocol interactions. After stage
admission, they refuse Protocol and participant selected regions in the entry's
static closure, with
`native-proof-control-profile`, `native-request-control-profile`,
`native-codec-control-profile` and `oracle-realization-control-profile`
respectively, before any candidate mutation. The closure starts at the selected
entry, its projected participants or the selected construction. It contains
every nested operation of a reached definition, including dormant arms, and
the definitions that the reached symbol references name, transitively:
applications, helper and local calls, and oracle and relation declarations.
Reachability is static: no selector is evaluated and no arm is pruned. A
declaration outside the closure, such as an uncalled helper with a Math
selection or an uncalled protocol with a Protocol selection, does not change
the judgment. One allowance of 100,000 operations and symbol uses bounds the
traversal, and exhausting it refuses with the same code.

Total `data.branch` regions are mathematical value computations, not conditional
protocol interactions. Stage admission checks every arm and excludes protocol
events from that total vocabulary. Event readers retain the complete selection;
checked projection and recursive computation realization preserve lazy execution,
captures and arm yields. No eager Boolean rewrite or target-specific bypass is
used. This does not widen reverse-request dependency reconstruction, structured
formal export or conditional protocol-event support: their separate profiles
still apply. In particular a request whose replicated dependency is an unsupported
selected expression refuses at request admission; a successful value selection
does not establish an event schedule or a sampling law.

## Formal interpretation and assurance boundary

`Zkc.Source.Region` provides typed operations with explicit callback inputs and
ordered result lists. Selected operation meanings interpret branches and finite
iteration; `Zkc.Source.Finite` models ordered domain admission and effectful
folds. Their laws preserve stopping behavior and interaction order within the
independent Lean model. They do not establish that native bounds, captures,
resource policies or executable control implement those meanings.

Independent Lean models and model-specific tools interpret their own region and
carrier contracts. Their correspondence results are separate from the current
native executable. See [implementation and evidence](../../compiler/control.md).

## Explicit local stops

Executable local code spells a stop as `["stop", site, reason]`. Reasons are
`reject`, `abort`, `exhausted`, `incomplete` and `refused`. All are terminal,
including inside a match or called algorithm. They produce no result or invented
yield. Continuing alternatives retain their normal result/resource obligations.

## Conditional completion extension

The native mathematical path also supports [conditional entry completion and
bounded local termination](completion.md). Its executable records have no automatic correspondence to an independent
formal carrier.

## Selected Protocol and mathematical regions

The registered selected-region forms are `protocol.branch`,
`protocol.participant_branch` and `data.branch`. Their common structural
interface has a selector followed by ordered explicit captures, ordered results,
an `alternatives` string array, and one closed single-block arm per alternative.
An `i1` selector has exactly `["then", "else"]`; an ordinary `!data.variant`
selector has exactly its declared labels in declaration order. Unknown,
repeated, missing or reordered alternatives refuse. No default arm is admitted.
A selected region has at most 512 arms, which equals the Data type language's
[formation profile](variants.md#type-and-value), so every variant that forms can
be selected over. A region with more alternatives or arms refuses with
`selected-control-limit` before its selector is read.

An arm receives its alternative's exact ordered payload types followed by all
capture types. Boolean arms have no payload. The selector itself is evaluated
once outside the arm; payloads are supplied only at selected entry. All arms
are checked, including dormant arms. Isolation forbids ambient SSA capture.
Each arm ends in the corresponding dialect's `yield`, with exactly the ordered
result types. Selected execution enters one arm, charges its work and effects,
and supplies its actual yielded values. Untaken arms perform no allocation,
query, message or other action. Effect freedom alone does not authorize eager
execution or speculation.

`protocol.branch` additionally has a unique `site`, a nonempty distinct `roles`
roster and one nonempty `output_roles` set per result. The selector must be
available at every participating role. Every action's complete participant set
must fit the roster, including holders and all receivers. Every arm must yield
each declared result component. Captures may transfer affine state once into
selected control; each arm checks its uses independently. A service reference
is an immutable alias of its exact outer capture root and cannot be yielded as
service authority. Nested control retains these constraints.

Availability is independent of agreement. Shared scheduling requires static
agreement, congruent admitted total mathematics, structural forwarding, or
entry obligations over exact immutable components. Native derivation reports
unresolved input groups with original native port, participant, complete
variant-payload projection and value/tag/collection-extent selection. A dynamic
extent requirement names its exact collection axis; a static type extent needs
no input equality. A statically constructed enum tag needs no payload equality,
even when the payload has ordered provenance. These groups are
requirements for actual entry admission; formation, a public flag, a producer
annotation and the existence of an API result discharge none of them. A common
enum tag establishes no payload equality. Local actions, entropy, received
values and unsupported provenance cannot establish common control. Calls
substitute actual ports and role maps through checked acyclic bodies. Repeats
retain initializer, recurrence and zero-path dependencies separately.

Native selected-control formation applies to each Protocol definition whose
actual static application closure contains a Protocol branch. It checks wrappers
under their actual argument and role substitutions, including branches in
retained dormant arms. An unrelated, uncalled definition cannot switch another
definition's admission policy. Branch-free generic iteration retains its
[joint count check](iteration.md); source-certified and named Entry admission
still derive and discharge the required common-input inventory independently.
Call-closure discovery and subsequent derivations share one cumulative work
allowance; discovery is not unmetered preparation for that derivation.

A demanded carry observation must agree initially and be preserved by its
yielded transition. These are simultaneous induction obligations over the
demanded slots, not permanent facts attached to equal initializers. Each
obligation belongs to the exact instantiated loop, slot, role association and
observation path; equal attribute dictionaries do not identify iterations of
different loops or helper calls. Cyclic dependencies may use the preceding
iteration's agreement only while all corresponding base and transition
obligations are checked. Nested recurrences retain their enclosing invocation.
Unknown state in an unrelated carry creates no agreement obligation.

Tag, guarded payload and extent observations project the initial and transition
values separately. Projecting a selected value rejoins the arm observations:
an identical known observation in every arm is independent of the selector.
Unknown observations cannot establish equality, and a Protocol branch's own
scheduling demand remains separate. Payload alternatives and ordinals remain
distinct; an
inactive constructor alternative has no payload obligation on that guarded
path. Its enclosing selected expression still requires tag agreement. An
at-most-one body uses its initial carry; a known zero exit forwards the initial
value and a known one exit forwards the transition. General exits retain the
count, initial and transition dependencies, including a possible zero path.
Analysis checks stored bodies even for zero counts, without unrolling runtime
bounds. Exhausted derivation work refuses with `common-control-capacity`;
missing provenance refuses with `common-control-provenance`.

Projection produces `protocol.participant_branch`, preserving the site and
alternatives, each participant's captures/results and each actual arm. Services
retain their owning participant's existing service-port identity. Independent
comparison checks selector, capture and payload association, every arm and
exact yields. Retained action records associate each arm label with its nested
actions; moving an action between arms changes its occurrence. A participant's
stop or Entry completion affects that participant alone.

Retained projection metadata records at most 256 arms for each Protocol
selected region. This bound belongs to the metadata alone: it is neither the
512-arm region limit nor a role bound. A projected unit whose region has more
arms refuses with `mathematical-projection` when its metadata is admitted.

`data.branch` has no Protocol roster or action permissions. Its inputs, payloads
and results must be total mathematical data, and every arm admits only installed
total operations and acyclic total helpers. It cannot contain a service, Local
call, ordered guard, logical handle or resource. `data.yield` closes each arm.
This form does not introduce an unregistered SCF operation or grant ordered
execution to Math. Projection places a Math selection, like other total
mathematics, only at the roles that demand one of its results; formation still
checks every arm of the source and of each participant. The projected comparison
reads the selection as one total value where a participant consumes it. That
value retains the selector, the captures, each alternative's payloads and every
arm's yields, so a changed selector, payload association or arm yield refuses,
as does a consumer that no longer reads the selection. Preparation and
participant comparisons keep each selection at its position. Polynomial observations requiring a selected degree adapter
remain an explicit unsupported profile. Numerical realization uses the
[recursive computation recipes](computation.md#realization), preserving selected
scope entry, arm-local work/allocation and independently checked payload,
capture and yield association through native Program execution.

Exact resource origins intersect corresponding arm successors. A legitimate
fresh branch result may have unknown formal-relative origin; unknown does not
prove an old-root recurrence. Zero trips retain the old root. Dependencies,
common-value congruence, reached facts and authentication use their own
transfer and join rules. Native control admission supplies no security theorem
or independent formal interpretation. Implementation and executable/realization
boundaries are recorded in [status](../../status.md).
