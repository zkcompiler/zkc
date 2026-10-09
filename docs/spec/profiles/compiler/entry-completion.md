# Conditional entry completion

This profile adds owner-local normal completion to the mathematical protocol and
participant machine, and bounded early termination to local loops. It introduces
no protocol-specific dispatch, retry exception or additional IR stage.

## Entry action

```mlir
%next = "protocol.finish_if"(%condition, %complete, %rng)
  {owner = "P", site = "decision"} : (i1, i1, !rng) -> !rng
```

Operand zero is Boolean. The remaining operands are exactly the owner's entry
result tuple, in declared output order. All operands must be available to that
owner. Results are exactly the affine tuple operands, in the same order and
types, under fresh SSA names. A copyable result operand remains usable through
its existing name. An affine operand is consumed on both paths.

False continues with the affine successors. True returns the tuple from that
participant's entry, skipping all its enclosing repeats and remaining actions.
Other roles do not learn the condition or return implicitly. A result declared
for several owners denotes a result port at each participant. Early completion
may return a different value at one owner's port; it neither changes a peer's
port nor guarantees equality between their results. A protocol requiring equal
results must express the communication and checks that establish equality. The action is
ordered and effectful; it cannot be speculated, erased as unused, or moved across
an observation. Unreachable suffixes remain subject to formation and
source/candidate checking. No successful branch removes another role's checks.

The same operation is used in protocol, participant, exec and physical profiles.
In a participant its owner must equal the participant role. A mathematical
function containing this action cannot be applied as a reusable component:
entry completion must never be silently retargeted by inlining. Reusable
component-local exits require a separate future scope contract.

A normal final return and an early return can expose different live resource
roots. Existing affine-use and repeat-origin invariants still apply. The attempt
host authenticates each configured RNG successor against its actual input root
on every return; an incorrect mapping is fatal. No extra equality with the
syntactic final return is inferred.

## Executable record and control boundary

Only `zkc.program` admits:

```text
["return_if", site, condition, entry_values, affine_continuations]
```

Admission checks the complete participant entry signature even inside nested
loops. This instruction is not a region terminator: the false path still needs
a final return or yield.

Inspection exposes a distinct conditional-return boundary. Advancing it checks
the exact origin and site before work, for both independent and joint execution.
Ordinary polling does not cross this boundary. One instruction is charged before
inspecting the condition; false-path binding uses ordinary retained-value
accounting.

A true return transfers the actual tuple through every active loop frame,
innermost first, using the existing returned-frame custody hook. It does not
restart a loop or charge skipped iterations. The root reserves result retention
before publication. A hook, budget or cleanup failure stops execution, preserves
reached effects and forbids publishing successful outputs. The backend removes
each leaving frame even on refusal, as required by its existing contract.

A successful early return retains its exact occurrence path and site. Attempt
reports include this coordinate, consumed work and the discarded prefix.
One-shot native execution reports the coordinate as `return_at` too; it is null
for a final return. In an attempt run, top-level `return_at` is null; coordinates
belong to each attempt, including one selected as complete by its policy.
Returning false in the host-selected completion port requests another attempt;
returning from `finish_if` alone does not request a retry or certify a proof.

The action has ordered effects and may skip the rest of the participant body.
Generic MLIR transforms that assume every block operation executes, including
loop-invariant code motion, require a preservation argument for this control
contract before they may run on these bodies.

## Transcript construction and independent checking

Constructed transcript state is an additional final entry output. Construction
adds its current successor to every conditional return, including returns in
otherwise event-free loops. Those loops explicitly carry the state. The
independent proof reader checks that every exit returns the current state and
that its false path binds the corresponding successor.

A completion cannot interrupt a pending challenge draw or an unobserved message.
Every reached observation remains in the transcript; no event is added for the
local return itself. A returned proof prefix may be incomplete and rejected by
the independent validator. Retry buffers remain private to the attempt host.
Authored transcript state remains ordinary typed data with explicit ordered
operations; its reached hash work is retained by the same control semantics.

## Joint execution

A returned role's later static steps are skipped. Reports record reached actions
only; omitted suffix steps are identified by the retained return coordinate and
the supplied schedule. Other roles continue their own programs. Loop agreement compares only live participating roles; when all loop
participants have returned, no further iterations run. A live communication with
a returned peer ends the joint run as `ReturnedEarly`, identifying the returned
and blocked roles. Unfinished roles are cancelled and reached work is retained.
If all roles return and no message remains pending, the run is `Completed`.
This host outcome is distinct from the returned completion data and from a
participant or driver failure.

## Bounded local termination

A `local.for` body may end in `local.condition` instead of `local.yield`. Its
leading Boolean SSA operand means continue; the remaining operands are the same
carried values and unchanged capture arguments as a yield. False returns the
carried values without another iteration. True advances only while the finite
upper bound permits. An empty range returns the initial values without running
the body or testing a flag. Both bound and work limits remain enforced.

The Boolean is an explicit use, separate from forwarded region operands.
`RegionBranchOpInterface` retains the existing loop entry/backedge/result
mapping; `RegionBranchTerminatorOpInterface` excludes the leading condition.
Affine carried roots retain the existing slot invariant on either edge.

Only the program format encodes this body as:

```text
["for_while", site, induction, lower, upper, carried, captures, body, outputs]
```

The body's final serialized yield contains the Boolean followed by the carried
values. A conditional body must end in this yield; a body ending in an
unconditional stop uses ordinary `for` encoding. Captures are explicit MLIR
forwarding operands and are omitted by the executable encoding.
A false condition ends this local loop, not the local function or participant.
This supports bounded searches without an unrelated body executing on every
remaining iteration. It grants no unbounded loop or arbitrary jump.

## Consumer boundary

A reader that does not implement conditional completion must refuse these
records. Format admission and execution checks alone do not establish a native
execution theorem or a cryptographic security result.
