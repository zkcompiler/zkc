# Independent participant runtime

This directory is a self-contained Rust module for the selected
`zkc.participants/1` tagged-array schema. It implements strict physical artifact
admission, immutable custody, typed SSA checking, stored calls, closed loops,
independent role execution, packets, resource frames and source-cut controller
support. It contains no cryptographic implementation. `tests.rs` uses an explicitly
mock service and does not establish security or external library correctness.

## Boundaries

The runtime is exported as `zkc_runtime::interactive`. It owns admission,
participant control flow and frame lifecycle. The `zkc-backends` crate implements
its `Backend` contract, while `zkc-tools::protocol` supplies the installed Lean
candidate checker, common-source schedule and transport driver. The runtime does
not depend on a cryptographic backend, avoiding a dependency cycle.

## Loading and custody

1. Install a trusted `Backend` implementation. Its `binding_signature` must
   match the independently resolved contract, nominal arguments and physical
   implementation. Unknown types, contracts, representations and undeclared
   operation symbols fail closed, including unused definitions. `/1` artifacts
   are refused; this module has no profile-migration decoder.
2. For generated artifacts use
   `admit_physical(source_bytes, candidate_bytes, &backend, &checker)`.
   `Correspondence::check_with_mapping` is the installed actual-source checker. It must
   establish source formation and the selected projection/physical correspondence,
   including parameter-name sets, resolved dependencies, mapped ports, lowered
   loop counts, and source action cuts. A hash match or an always-successful
   callback does not establish that contract. Source/candidate byte slices are
   actual inputs, not artifact-declared claims. Checked bytes and parsed code are
   owned immutably by the returned `Admitted` wrapper.
3. Independently supplied participants use `admit_supplied(candidate, &backend)`.
   This uses the same physical/typed/installed-contract checks but deliberately
   carries `checked_source() == None`. It certifies no source provenance or
   correspondence. Both APIs refuse logical stage; there is no reference-only
   logical-stage bypass in this module.
4. Obtain `admitted.entry("entryName")`. Each `EntryRole` exposes its exact ordered
   `(argumentName, PhysicalType)` inputs, result types, instance and parameters. Construct
   `Runner::new(&admitted, entry, role, session_id, backend, values)` with only that
   role's input values, in exactly that order. No other role's environment exists
   in the runner. Arity/type errors fail before entry execution. `LoadError`
   returns both the error and backend custody.

`Admitted` does not expose mutable code or admit an already-constructed public AST.
Every `Runner::new` rechecks installed signatures, so a different backend cannot
reuse admission with incompatible contracts. Backend implementations and source
checkers are trusted installation code, not untrusted plugin closures.

Public parameter strings are canonical bounded naturals, names are exact/unique,
and different roles of one instance have identical parameter maps. A participant
artifact does not contain source protocol parameter declarations. Exact parameter
*name sets* and their relationship to physical loops require the source checker
for compiler output, or the caller's explicitly selected supplied-participant
policy. The runtime does not invent those missing declarations.

## Small backend contract

`Value: Clone` has four required methods:

- `type_name() -> &str`: exact schema type name, backed by a trusted typed enum.
- `physical_type() -> PhysicalType`: intrinsic nominal domain and representation.
- `validate_serializable() -> Result<(), BackendError>`: validate the whole public
  representation, including nested contents. Keys/capabilities are not messages;
  a private object disguised as `field` must not pass this method.
- `retained_bytes() -> usize`: stable, conservative payload bytes. Shared immutable
  backing is counted in full for each retained handle. Clones should be cheap
  Arc/handle clones and must not clone resource authority or random state.

`Backend` supplies explicit binding signatures, value validation, frame entry
and exit, and atomic operation application. `Invocation::binding` always has a
complete declaration. There is no profile-based signature or type constructor;
`LogicalType::new`/`parse` and `PhysicalType::new`/`parse` require the nominal
identity, and `PhysicalType::default_for` selects storage for that explicit type.
There are no whole-prover or all-environment callbacks.

`validate_value` checks variant/type consistency, canonical representation and
per-value bounds. This method and serializability validation are read-only and
must not mutate service/capability state. Validation occurs for entry/frame
arguments, operation arguments/results and message values. The entry frame hook
must additionally check this role's declared input policy: expected table/key
shape and public parameters, setup/key/subject identity, actual capability
issuance, ownership, generations, and any required entry public input agreement.
The runtime cannot validate an opaque backend's field/table/key internals.

`enter_frame(&Frame, &[Value])` receives only actual arguments. Entry, child call,
loop iteration and local-function frames have runtime-minted IDs and parent IDs.
Frames expose role, instance/call/iteration origin, parameters and the input
signature, never the role environment. Loop arguments are carried values followed
by explicit immutable captures. A local function runs in an additional restricted
frame and each kernel sees only its own actual operands. The backend owns the
full authoritative resource store, but must check BOTH the active frame's view
and these explicit operands before using any stored resource.

Distinct SSA names can alias a slot. Static affine checking rejects repeated uses
of one consumed name; it does not replace actual alias/generation checks. The
adapter must check real issuance and generation on use, preserve the unaffected
frame, and enforce instance/owner binding. No public runtime API mints capability
issuance. Passing a handle between repeated calls does not create a fresh tape.
Affine values must be loop-carried; invariant affine captures are rejected.

`apply(&Invocation, &[Value]) -> Result<Vec<Value>, BackendError>` runs one
allowlisted mathematical kernel. Results are independently checked for exact
arity/type/representation before binding. Every consume must advance the backend's
authoritative state before any subsequent failure. A returned error is not rolled
back. An adapter must preserve both completed state transitions and unaffected
resources. It should use the actual arkworks typed values and checked codecs;
reference arithmetic in this module's tests must never be substituted for that
adapter in production.

After every successful entry, `leave_frame` is called on return, stop or explicit
cancellation, including nested failure unwinding. It receives returned values only
on success. An out-of-order `leave_frame` leaves all views unchanged. For an
ordered exit, `leave_frame` must pop its frame even when it returns an error, must
validate any returned capability authority, and must never undo completed resource
transitions. A failed `enter_frame` must leave no active child frame. Cleanup
errors are retained as local stop diagnostics. Frame admission itself validates
and focuses authority; it must not draw randomness or run a source algorithm.

Recover the authoritative backend with `runner.into_backend()`; this explicitly
cancels/unwinds an unfinished runner. `runner.cancel()` also unwinds. Dropping an unfinished runner also
unwinds all frames with `Cancelled`, even if a cleanup hook returns an error.
Explicit cancellation/recovery is preferable when the host needs the diagnostics
or backend custody; implicit Drop cannot return cleanup errors. Panicking/malicious
backend implementations and process termination are outside this interface's
normal-result contract.

## Actions, packets and origins

`poll()` exposes `Action::Local`, `Send`, `Receive`, `Returned`, or `Stopped`.
Repeated polling of the same pending/terminal action is stable: it performs no
instructions, frame calls, capability transitions or draws. Initial polling may
perform bounded administrative call/loop/return transitions until it reaches the
next cut. Those transitions do not run kernels.

- `execute_local(&cut)` executes exactly one whole source local function, never
  the following local action. On a failing kernel it stops immediately and runs
  no suffix. The stop is observed by the next `poll` (or `is_terminal`). A successful
  method return means the requested cut was processed, not that its algorithm
  succeeded. Wrong action/cut returns an error without executing a kernel.
- `take_send(&cut)` consumes one pending outgoing packet and transfers custody to
  the caller. It does not observe or advance a peer.
- `deliver(packet)` advances exactly one matching receive. Envelope/type/value
  mismatch leaves the request and execution counters unchanged. `check_delivery`
  provides a non-consuming preflight for the controller.
- `Returned` is distinct from local stop, cancellation, resource limit, and
  `StopKind::Incomplete`. The reserved `stop` reason `incomplete` implements the
  owner-selected foreign syntactic stop encoding; it contains no remote reason.
  A peer's dynamic stop is never communicated implicitly.

`Envelope` binds host-agreed session, entry, executing instance, an ordered
call/loop path, message site, schema, sender and receiver. Calls identify source
call sites and selected child instances; each loop appends site and iteration,
including empty-state loops. Nested calls and loop iterations retain their order.
Packet type and complete payload are separately checked against the receive
signature. A packet from an earlier child call/iteration/session cannot satisfy a
later receive even when schema and payload match.

The host must create a unique session ID for each execution and agree on it with
the intended peer, together with the admitted compatible programs/public instance
configuration. Reusing session IDs permits replay; this module performs no
transport authentication, session negotiation or cryptographic packet protection.
It checks equality against the runner's expected domain. Host/controller custody
of returned packets and retries after failed network delivery are explicit.

`Origin::domain_bytes`, `Envelope::domain_bytes` and `Invocation::domain_bytes`
use distinct tagged JSON arrays with decimal strings for naturals. These are
unambiguous bytes, not a cryptographic hash. The local-operation domain includes
session/entry/instance/path, role, local site, logical function origin, operation
site, binding contract/static arguments, attributes and selected parameters. Packet payload wire codecs and
wire-byte limits belong to the installed adapter/transport; the runtime consumes
typed values and does not guess an encoding for arkworks objects.

## Source-order driver

`zkc-tools::protocol::Schedule` traverses the admitted common source and selects `DriverCut::Local(cut)` or
`DriverCut::Message { send, receive }`. `drive_cut(left, right, &cut)` processes
exactly that cut, after verifying pair and expected pending origins. A message
preflights both ends before consuming the send. The helper does not infer source
order from readiness, fuse adjacent local functions, or poll a peer during a
local action. Each backend remains separately owned. The caller stops its joint
reference traversal when the selected observation says to stop; an independent
role can subsequently progress under a different controller.

The generic common-source traversal, actual Lean/native correspondence check and
source action schedule belong to `zkc-tools::protocol`. This helper is the executable controller
primitive, not an implementation of those source semantics or a liveness theorem.

## Fixed limits

The owner-aligned artifact ceilings are 1 MiB, JSON nesting 64, array length and
module instructions 32768, definitions per declaration list 4096, ports 1024,
operation attributes 16384,
public parameter and individual loop count 1048576. Additional fail-closed parser
limits are 200000 JSON nodes, raw string length 4096, identifier length 128, stop
reason length 1024, and block nesting 64. `ErrorCode` identifies the failure class.

Runtime ceilings are 64 active frames (including local frames), 100000 calls,
100000 total iterations, 1000000 instruction units, 16384 retained values and
64 MiB per individual value. Default host policy permits 64 MiB live retained
payloads and 256 MiB cumulative retained payload accounting. A
local instruction, participant instruction, loop header and each executed loop
yield count toward fuel. `Runner::new_with_value_budget` permits a host to select
live and cumulative payload budgets before entry admission; `Runner::new` keeps
the defaults. This does not raise individual-value, structural, wire or native
kernel limits. Source code cannot alter the policy. Zero budgets and checked
addition overflow remain fail closed. Module calls
are acyclic, but combined calls and nested loops are still checked at runtime.

Allocation accounting covers retained runtime environments, loop capture metadata,
local temporaries and terminal returned values; shared backing is conservatively
counted repeatedly. `Invocation::max_output_bytes` bounds acceptable new output
payloads and the backend must check it *before* allocation. Parser/control metadata
is bounded structurally. This is not a reservation of every std allocation,
transport-owned/polled clone, backend authoritative store, or upstream PCS scratch.
Rust/OS allocation aborts and external library panics are separate limitations;
backend-specific per-operation/total memory limits remain required. Typed values
must be immutable with stable size reports. Large table handles should share
backing to avoid repeated deep copies.

## Validation scope

The crate tests cover malformed decoding, installed contracts, stages,
symbol/signature/SSA/loop closure, role isolation, source checker custody, every
message envelope dimension, malicious private payloads, repeated/nested calls and
loops, zero and empty loops, pending stability, actual alias/generation failures,
consumed failure prefixes, unaffected frames, cancellation and controller cuts.

These unit tests use mock backends. The separate interactive integration suite
compiles actual source, checks actual candidates in Lean and executes real
arkworks operations. Neither suite establishes native formal refinement,
cryptographic security or unbounded progress.

Current types retain full nominal domain identity and selected representation.
BLS G1 points have validated curve representations. The historical additive-Fr
group, its scalar kind and its public backend are absent from the installed API.
`transcript`, RNG and nonce handles retain their affine/resource contracts through
explicit local operands, successors, calls and loops. Independent source
correspondence remains separate from physical admission. `zkc_runtime::logical`
provides the bounded tree codec and session-independent occurrence helpers.

Logical construction trees use separate `logical::TreeLimits`: 16 MiB total and
per-string ceilings, 32768 array entries, 200000 nodes, depth64 (root0). Public
wire hex may exceed a source identifier's size. Source JSON admission continues
to use its existing 1 MiB total/4096-byte-string limits.

## Structured local control

Physical local function bodies admit the same local-region records as source:

```text
["if", site, condition, captures, then_body, else_body, outputs]
["for", site, induction, lower, upper, carried, captures, body, outputs]
["yield", values]
```

Both branches and every loop body are admitted recursively, even when not reached.
Sites are unique across the entire function. Each region has an isolated SSA scope:
only explicit captures and region arguments are available. Each region must end in
`yield`; the function must end in `return`. Conditional branches yield identical
ordered physical types. Conditional affine captures consume the enclosing binding
once; each branch is checked independently. Loop captures must be non-affine.
Affine values can instead be carried as `[region_name, initial_name]` pairs and
returned through the ordered yields. Admission rejects duplicate uses, hidden free
variables, overlapping region arguments, and representation-view escapes.

The runner executes only the selected branch. A loop evaluates its two index bounds
once, executes the half-open range, and returns the initial carries on zero or
inverted bounds. Each bound is at most `Limits::PARAMETER`, the trip count is at most
`Limits::LOOP_COUNT`, and global instruction/iteration limits still apply. Deterministic bound failures
report `exhausted:local-bound-limit`; cumulative machine budget failures retain
`StopKind::Limit`. An iteration-budget failure retains the attempted iteration
path without entering its body. Bodies
remain compact; no trip-count expansion occurs. Local controls are refused in the
participant body, whose protocol-level control grammar is unchanged. Native helper
expansion must expand helper calls inside regions while retaining the regions.

Every selected region is a real backend child frame, with its actual enclosing
local frame as parent. Its origin appends `["if", site, "then"|"else"]` or
`["for", site, decimal_induction]`. Local call and logical function identities remain
in invocation domains. Resource generations advance through actual ordered
operations; a failure neither runs subsequent operations nor rolls back completed
effects. Accepted frames are unwound, and cleanup failures remain explicit.
Backend values implement `control_bool`, `control_index`, and
`from_control_index`; their default implementations explicitly refuse. The native
backend provides exact bool/index access with no cryptographic service call.

Each executed operation, control, yield, and return costs one instruction. A
`release` costs zero and retains the existing conservative ghost charge until its
own region exits. A loop iteration attempt charges one iteration before frame/value
admission; no iteration is charged for a zero-trip loop. Local regions do not
increment the protocol-call counter. Stack limits include participant frames, the
local function frame, and all active regions. Each region entry charges its input
bindings, including the loop induction value. Each operation and enclosing control
result binding charges its results. Next-iteration carries are charged at the next
entry; final carries are charged as enclosing results. Loop captures need no extra
metadata store, since the parent environment retains them. The native backend
retains its existing 512-byte conservative scalar charge, including indices.
Region exit releases its live and ghost charges; cumulative bytes never decrease.

Installed-operation checks, implementation-role inventories, and public-validator
resource screening traverse both branches and nested loops. Ordinary source
correspondence remains the independently installed checker's responsibility; these
runtime checks alone do not establish source/candidate equivalence.
