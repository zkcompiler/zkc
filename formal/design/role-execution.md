# Direct source roles and independent role programs

`Zkc.Source.Protocol.Role` defines one role's open meaning directly over every
constructor of `Zkc.Source.Protocol.Program` and every stored protocol definition.
`Zkc.Compiler.Role.Syntax` and `Meaning` define a separate role grammar and
interpreter. `Projection` extracts that grammar mechanically and proves exact
effect-tree equality with the direct source-role interpretation. The existing
`Zkc.Compiler.Participant` scheduled target and its joint theorems are unchanged.

## Inputs and observations

`Source.Protocol.Role.Environment Value self ports` can read only a
`Var ports (self, ty)`. The full port list is static typing metadata; it contains
no tuple of peer values. This same focused representation is used for entry
arguments, local call capture, protocol results, bind and loop accumulators.
`Environment.skip` extends metadata for a foreign port without a placeholder
value. `capture` selects only declared operands. `prepend` restores the caller
with only that role's results.

The two interpreters share a typed observation interface, not a source evaluator:

| Request | Operands | Reply |
|---|---|---|
| local | location, actual local definition reference, owned arguments | arbitrary typed local result |
| send | location, schema, receiver, owned value | Unit acknowledgement |
| receive | result sort, location, schema, sender | arbitrary typed incoming value |
| stop | location, own reason | Empty |

Locations retain entry, selected binding, invocation/iteration path and source
site. Role identity is selected by the role program and can be attached using
`Location.origin`. No receive contains a sender operand, sender value, sender
state or packet obtained by executing an honest send. Independently supplied
programs can use this same target grammar and interpreter.

The target has separate `send`, `receive`, `localCall`, `stop`, `incomplete`,
`ret`, `invoke`, `repeat`, `bind` and metadata-only `skip` constructors. It has no
joint pending-packet index. In particular, `send` does not extend a receiver's
runtime context. Extraction follows it with `skip` solely to preserve source
indices for the remaining local operands.

## Control and definitions

An owned local action executes; a foreign local action is erased. Its dynamic
private stop cannot cancel this role. An owned syntactic stop issues an own stop
request and retains its reason. A foreign syntactic stop leaf has no source
continuation or result: its direct meaning is `Proc.halt .incomplete`, and its
target is `Program.incomplete`. No remote reason, stop site or fabricated result
is exposed at that terminal boundary. Bind, invoke and repeat propagate this
terminal without running a normal suffix.

`projectDefinitions` retains the actual acyclic table, exact signatures and
references. Every call executes its stored body, using its selected child binding
and an appended invocation frame. Return restores the parent binding and path.
Loops retain their body and fixed public count; each iteration appends its actual
index and threads only the focused accumulator. Zero iterations do not enter the
body. Role remapping, recursive protocol tables and global choice are not in the
current source grammar and are not added by this implementation.

`Source.Protocol.Role.Runtime.handler` resolves local calls through actual
`Source.Definitions.operation`. Local regions retain their own branches, nested
local calls, iterations, stops and primitive meaning. A binding selects a
`LocalImplementation` with one local state type. No runtime entry receives a
family of peer states. Every service failure retains its post-state, ordered
local events and enclosing location. These interfaces do not audit arbitrary
host-language closures or establish cryptographic noninterference, resource
admission, or truthful service replies.

## Proved correspondence

- `denote_project`: structural equality under a compositional call-table law.
- `denote_projectDefinitions`: discharges that law for every actual stored table,
  reference, binding, path and focused input. No assumed projection equality
  remains in this theorem.
- `run_project`: equal complete executions for any common completed typed handler.
- `run_project_runtime`: instantiates actual local definitions and arbitrary
  binding-selected primitive implementations and completed incoming services.
- `run_project_related`: transports the result under an actual `HandlerRelated`
  law, including residual state and selected event observations.
- `advance_project`: equality for arbitrary polling policies, including retained
  cursors, missing-input suspension and budget yield.

The source-role module has no compiler dependency. Target meaning and the
independent target consumer have no dependency on the direct source-role
interpreter or projection. Sharing the value context, `Proc`, and observation
signature does not identify the syntax traversals or define one interpreter by
the other.

## Suspension and finite denotation

`Compiler.Role.Runner.advance` runs a cursor for a budget of exposed requests. A
cursor holds the remaining effect tree, local state and prior events. `finished`,
`suspended` and `yielded` are different result constructors. The runtime polling
adapter returns `none` only for missing ingress, as proved by
`Runtime.poll_none_receive`. `advance_missing` preserves the exact pending
request, continuation, state and events. `RunResult.resume` retries that cursor;
completed prefixes are not replayed. An explicit ingress failure can instead
return `some` stopped execution, retaining its actual effects.

`advance_complete` proves equality with `Proc.run` under a completed strategy and
`Within fuel program`; `drive_complete` supplies the actual runtime adapter.
There is no unconditional network progress claim. The budget does not bound
initial denotation cost, memory, or work inside an atomic local call. The cursor
uses Lean closures over a finite `Proc`; it is not a serialized native call stack.
A native stack/CFG runner needs its own representation correspondence.

## Joint execution boundary

The maintained joint participant theorem remains the exact scheduled theorem.
`Compiler.Role.Simulation` adds a separate source-cut connection between different
joint and endpoint trees. Structural alignment is proved through every typed
constructor and actual stored table. `Driver.stored_trace_simulation` derives
successful cuts from an actual joint handler and proves endpoint reachability
and residual alignment under explicit primitive reply coupling. It does not
assume whole-program equality. Actual local and message-cut laws retain stopped
effects, send-before-receive emissions and the sender's live continuation when
reception fails. An unselected cursor remains unchanged.

`Tests.RoleDriver` checks `P:a; V:check; P:b`: the joint runtime stops with one P
action while independent P can still perform b. This rules out freely completed
endpoint states as the observer of a stopped joint run. One recursive theorem
assembling all heterogeneous role states, the final failure half, global origin
and full observer is still unproved. The proved prefix and individual failure-cut
laws are the scoped connection; neither native scheduling refinement nor arbitrary
terminal equivalence follows from them. Hidden shared services, fusion across a
cut and fairness require additional contracts.

## Restricted resources

`Semantics.ResourceView` uses a heterogeneous store `(slot : Slot) → Cell slot`
and a selected-slot predicate. Its handler sees only the dependent selected
view. Restriction and installation satisfy lens equations; `run_frame` and
`run_scoped` preserve the actual residual selected state, complete outcomes/events,
and every outside cell. Stops retain consumption rather than rolling it back.

`Compiler.Role.Resources.scopeRuntime` applies that adapter to actual selected
local implementations and send/receive services. `run_project_scoped` connects
direct source-role execution to projected stored roles, including stop origins.
`Tests.ResourceView` and `Tests.RoleResources` exercise heterogeneous tuples,
reply-dependent continuations, alias/generation refusals and failed consumption.
These generic confinement laws do not prove native capability authenticity or
physical non-aliasing. Those remain explicit backend checks and test obligations.

## Controls and native adoption

`Tests.RoleProjection` covers stored protocol calls, caller binding restoration,
nested paths, bind, mixed accumulators, zero/positive repeats, each message role,
hostile ingress, outgoing/local failures, own/foreign stops and suspension.
`Tests.RoleTarget` independently authors a heterogeneous target with actual local
branches and nested definitions and checks resume after partial progress.
`Tests.RoleIsolation` uses an uninhabited foreign private sort: no joint input
environment exists, but both receiver interpretations execute arbitrary ingress
without that value.

The native [interactive path](../../docs/compiler/interactive-execution.md)
implements owned operands/results, receive destinations, resolved instances,
explicit incomplete/stop and resumable stacks. Physical lowering retains control
and origins. The independent portable consumer is in `Tools.Interactive`; it
checks the actual candidate and runs a source reference without importing the
native compiler. The executable checker, typed theorem and native differential
comparison are three distinct results. Raw decoding, multi-result elaboration,
role remapping, native stack refinement and checker soundness are not proved by
the typed projection theorem. Full ExecutionProof bodies remain future work.
