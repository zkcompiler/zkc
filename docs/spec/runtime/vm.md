# VM execution

This contract covers admitted `zkc.program/0` programs, the runtime instance and
installed backends. The [program format](../formats/program.md) owns syntax and
structural checks. [Capacity](capacity.md) owns limits and metering. Hosts own
application authorization, transport and scheduling between participants.

## Program, instance and evaluator

`vm::Program::decode` checks the entire retained artifact without a backend. The
result owns its exact bytes and immutable typed code. Local functions use
positional operands and shared region layouts; participants retain named SSA
registers and shared loop-input layouts recorded during admission.
Loop frames use those admitted types in induction, carried-value and capture
order; the evaluator supplies actual values, not inferred port types.
This is an internal representation of the admitted program, with the
same instruction, frame, failure and work boundaries.

`Program::check_installation` is an optional deployment preflight. It checks
Boolean literal support, service interfaces and exact installed operation
signatures. It transfers no handles or authority to execution. Each instance
links its own backend, including operations in retained dormant definitions,
before entering any frame. Linking is read-only: it cannot draw randomness,
consume resources or validate invocation-dependent attributes early.

`interpreter::Runner` evaluates one role. An internal VM instance owns its
backend, linked handles, reached-call preparation, retained-value ledger,
capacity accounting and entered frames. The interpreter owns program counters,
SSA values, continuations, pending actions and control-dependent public
provenance. It cannot mutate the instance's ledgers or backend directly.
Opaque value scopes let the VM track binding counts and deferred storage
charges. The evaluator holds each scope alongside its value environment and
reports binding lifecycle events; it supplies no accounting totals.
Value scopes are independent of backend frames:
arguments can be retained before entry and returned backing can survive exit.
The terminal tuple is the exception: its scope stays in the VM while the
evaluator exposes the values for repeated inspection.
Immutable code may be shared; execution custody remains independent.

Return handoffs own their values and backing references together. Only the VM
creates or alters a handoff; releasing it consumes the handoff object. The
evaluator must release it through the originating instance on success and
failure. This internal obligation is not automatic destruction or a sandbox
against an incorrectly implemented evaluator.
Normally the producer creates the handoff, closes its environment and exits
with it retained. The receiver retains bindings before releasing the handoff.
Root completion reserves the terminal tuple before frame exit.

Loading checks, in order: hard budget ceilings, session syntax, installation,
entry and role selection, then actual inputs and entry-frame admission. A load
failure returns backend custody and the work already charged. Successful loading
returns an entered entry frame and its admitted inputs, and executes no program
instructions. The VM owns this complete admission sequence, including cleanup
on refusal. It also owns Boolean and variant construction, checked variant
decomposition and local range limits; the evaluator chooses and walks control
flow. Participant count checks use one VM operation; actual loop entry uses the
checked count after host agreement or local control selection.
Structural admission and installation do not
prove compiler correspondence, cryptographic correctness or protocol security.

## Calls and authority

A reached operation passes its exact resolved binding, static attributes,
logical origin, site and ordered actual operands. The instance derives authority
from its active frame and stored role, validates operands and charges their read
extent before calling installed code.
`CallContext` exposes these facts for operand-cost estimation; `Invocation` also
supplies the remaining output allowance and current retained-backing evidence.
No operation receives the evaluator's environment or arbitrary ancestor values.

The backend validates current policy, setup authorization and resource custody
at use. A prepared handle establishes code and signature facts only. Per-call
preparation may retain checked static facts only at the original reached
validation point. Unexecuted branches cannot acquire invocation failures through
preparation. Scratch arguments are cleared on success and failure; only empty
buffer capacity survives between calls.

The instance checks output arity, complete physical types, backend validity and
capacity before retaining results. Shared validation evidence applies only to
unchanged immutable backing. It never substitutes for capability issuance,
current generations, setup authorization or service-root custody.
[Service queries](services.md) keep their separate exposed cuts and reply bounds.
The VM resolves each query port against the active frame's service interface,
including its contract and resource input position, before consulting a provider.

Installed operations may consume randomness, mutate transcript state, advance
resources or refuse after a partial effect. A numerical realization must establish
its applicable effect and failure properties; a binding or mathematical equality
alone grants no permission to reorder these observations.

## Frames, observations and cleanup

The instance mints immutable frames and derives each parent from its active
frame stack. Only its latest outstanding frame proposal may attempt backend
entry, once. Frames from another instance, superseded proposals and already
attempted frames cannot enter. Frame custody uses object identity; equal
instance-local IDs and diagnostic metadata do not establish it.
Entry frames carry the admitted service interface. Participant loop
frames inherit that interface; local calls receive their explicit operand view.
Backend entry atomically checks custody and leaves no child active on refusal.
Only a successful entry pushes the VM frame. An exit must match the innermost
frame. Backend exit removes that view even when output validation or cleanup
reports an error; the VM removes its matching frame too.

Polling a pending action is stable. Hosts explicitly execute local work, answer
service cuts and move messages. Pure inspection neither advances execution nor
invokes backend hooks. A wrong action kind or cut identity is rejected before
preparing an unpolled action; a refused control request does not close the public
preparation prefix. A receive validates the session, role, entry, occurrence,
envelope and actual payload; independent participant values are not identified
merely because their declared types agree.

Failure retains the completed prefix. Stops record the reached origin, role,
site, primary cause, optional local context and ordered cleanup errors. Failure
and cancellation unwind entered frames in reverse order. Resource consumption
and messages are not rolled back, and a local stop does not signal a peer.
Backend recovery first closes the execution. Dropping an abandoned instance
also cancels remaining views; destruction cannot return cleanup diagnostics.
These contracts assume trusted backend hooks return normally.

Return values remain available for repeated terminal inspection. If root
reservation or exit fails, the VM releases terminal retention and preserves
the primary failure and cleanup order. A completed or stopped execution cannot
be reused as a fresh proof invocation. Host acceptance
and publication follow their separate [proof](proofs.md) and
[Entry](entries.md) contracts.

## Preparation and alternate engines

`PreparedComputations` is an explicitly bounded store for successful public,
deterministic local computations of the exact admitted executable. Host-authorized
public inputs and the interpreter's control provenance restrict eligibility.
Backend installation independently promises determinism and compatible work
checkpoints. The VM classifies installed deterministic code and owns bounded key
construction and opaque recording snapshots. The evaluator tracks public control
provenance and publishes a successful record only after frame exit succeeds.
A cache hit preserves outer frame hooks, cumulative charges,
subsequent frame IDs and the normal result handoff. Reuse requires compatible
policy and sufficient remaining capacity; otherwise the original body executes.
Private state, resource authority and proof inputs do not become shared state.

An alternate evaluator for the same admitted artifact must preserve outputs,
ordered interactions, refusals and stopped prefixes, resource successors,
cleanup and the applicable metering contract. It may change dispatch or storage
implementation while preserving those observations. Optional instrumentation
counts describe actual implementation work and may differ from metered work.

A checked compiler realization may instead produce a different physical program
with an explicitly justified work or storage contract. This is a compiler
transformation obligation, not permission for an evaluator to silently fuse
instructions. Numerical Kernel IR belongs at that realization boundary.
Generated native code requires trusted installation and a checked representation
ABI; a digest alone establishes
identity, not executable safety.
