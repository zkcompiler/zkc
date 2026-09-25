# Scheduled participant lowering

This profile lowers [resolved common protocols](../source/common-protocols.md)
to typed, scheduled participant instructions. It separates sends from receives,
restricts operand access by role, and retains shared calls and fixed public loops.
Its complete-execution theorem covers every constructor of that source subset.

The target is one structured schedule containing participant-local instructions.
It is not yet a collection of separately deployable role modules. The maintained
modules are [syntax](../../../../formal/Zkc/Compiler/Participant/Syntax.lean),
[meaning](../../../../formal/Zkc/Compiler/Participant/Meaning.lean),
[projection](../../../../formal/Zkc/Compiler/Participant/Projection.lean) and
[execution](../../../../formal/Zkc/Compiler/Participant/Execution.lean).

## Local environments and calls

For a port context `Γ`, a participant's environment has type:

```text
LocalEnvironment(Value, role, Γ)
  = {sort} -> Var Γ (role, sort) -> Value sort.
```

It contains no accessor for another role's value. The global port list remains
static type metadata. The joint driver holds a family of these local
environments, not one environment that it passes to every participant.
`separate` restricts the source environment to this family; `assemble` exposes
the family to the joint observer. They do not define native buffer layouts.

Local computation arguments are evaluated by `readLocal` using only the active
role's environment. Protocol-call capture maps each declared callee reference
back to an operand at that same role. `capture_local` proves that changing peer
environments cannot change this role's captured inputs. The binding of the
declared result tuple extends each role's environment at its own ports.

The target retains actual local definition references and a separate acyclic
table of scheduled protocol bodies. `projectDefinitions` translates each stored
body and preserves its reference position. Invocation selects the child's binding
and extends its path; the normal suffix restores the caller's binding and path.
It neither clones a body per call nor resets participant state.

## Communication and packet state

A transfer fixes a site, schema, sender, receiver, domain sort and proof that
the roles differ. The target program is indexed by either no pending transfer
or one pending transfer. Lowering replaces a common message with:

```text
send transfer senderOperand
  receive transfer
    continuation(receiverResult)
```

`send` reads the sender's operand and requests a packet from the selected send
service. Its successful continuation holds that packet as driver state.
`receive` calls the receiver's service with the packet, then binds the actual
received domain value at the receiver's port. A packet is not an operand of the
local domain language. The receiver result need not equal the sender input.

`Program.pending_receive` proves that a target with a pending transfer has the
receive constructor. A normal return, local computation, child call or another
send cannot occupy that position. The indexed transfer ties reception to the
actual route and schema; a wrong route cannot be substituted merely because
its packet representation has the same type.

This restricted packet discipline implements the selected synchronous reference.
It does not mandate a single in-flight packet for every future execution profile.
Interleaving transfers, cancellation or asynchronous delivery needs a different
target/schedule correspondence. Typed syntax supplies no codec, authenticity or
cryptographic resource-ownership theorem.

## Meaning and preservation

The target interface has four kinds of request: local computation, send, receive
and stop. Each runtime request receives only the selected role's private state.
The handler lifts its actual effects into the joint observation. It executes
local bodies through the existing local-definition meaning and sends/receives
through their separate services. It does not invoke the common-protocol runner.

`expand` interprets a common message as two target requests; local calls and stops
retain their meanings. The proof is factored into three connections:

| Theorem | Established connection |
|---|---|
| `denote_project` | Structural source translation agrees with operation expansion, assuming the actual callee relation |
| `denote_projectDefinitions` | The translated stored table supplies that relation for every valid callee reference |
| `handler_expand` | Executing the expanded requests equals the selected common handler, including failed send/receive effects |

The resulting theorem `run_project` states:

```text
targetRun(runtime, locals, projectDefinitions(protocols), selected, entry,
          separate(inputs), initialStates)
  = sourceRun(runtime, locals, protocols, selected, entry, inputs, initialStates).
```

Equality includes returned port values or the stopped reason, every role's final
state, ordered tagged events and stopped origin. It holds for arbitrary role and
domain types, packet representations, actual local/protocol tables, runtime
services, initial values and states, and all fixed natural loop counts. Roles
need decidable equality for the joint state update. Inputs must be related by
the displayed separation; unrelated native bindings receive no guarantee.

Loops retain one target body and carry actual accumulator values. The proof
uses the existing interpretation/iteration law, rather than unrolling a bounded
test corpus. It also covers `bind`, nested protocol calls and source stops with
no events. Local branches remain inside stored local computation bodies.

The source and target reuse the same `PIR.Proc` execution meaning. The only core
addition is the ordinary `Execution.follow_return` identity lemma; no execution
definition or cryptographic assumption changed.

Interface-request counts are not preserved: one common message expands into two
scheduled requests. `expand_within` bounds each expansion by two requests, and
`within_projectDefinitions` transports a source bound `B` to a target bound
`2 * B` using the existing interpretation-bound theorem. This counts scheduled
interface requests, not arithmetic or work inside local services. Concrete
source/target phase policies still need their own interpretation-admission law;
execution equality alone supplies neither that law nor unchanged certificates.

## Evidence and compiler handoff

[Projection controls](../../../../formal/Tests/ParticipantProjection.lean) compare
complete shared-call and loop executions for arbitrary services, and evaluate
concrete three-role cases with different state types. They retain changed receive
values, local/send/receive failures, nested stopped origins, caller-binding
restoration and iteration paths. An independently authored target exchange and
a same-signature alternative body show that execution uses the supplied target
table. A request-count control has three source requests and four target requests,
and rejects reuse of the old bound. These are Lean checks, not new MLIR/Rust
differential or performance results.

The next production-facing step is extraction of separately callable role modules
and their public coordination structure. It must retain the established schedule
and complete stopping behavior, then connect actual symbols, inputs and source
sites to this resolved target. A source-level proof does not bind emitted native
code to these subjects. The existing finite native/prototype evidence remains
separate until the matching operations and differential tests are implemented.

Global choice, role remapping, independent endpoint artifacts and asynchronous
progress remain open. Local-effect, information-flow, resource, sampling and
codec admission remain separate contracts even though raw execution is preserved.
The target's global port metadata may be compacted during role-module extraction;
retaining it here does not require keeping foreign value slots in native storage.

*Design context (informative).* The separation between local computation and
global coordination follows the endpoint-projection questions studied by
[Pirouette](https://people.mpi-sws.org/~dg/papers/popl22-choreographies.pdf).
That work's out-of-order and deadlock results are not inherited here: this profile
preserves the selected ordered failure semantics. Production callable definitions
should keep [MLIR symbol references](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/)
distinct from SSA operands and use explicit region inputs; this proof does not
choose a final dialect split or establish those native interfaces.
