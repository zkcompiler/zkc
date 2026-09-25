# Located calls and shared control

This profile specifies a resolved local call's contribution to a synchronous
joint execution, and agreement checks for separately bound control values.
It uses [shared definitions](definitions.md) and the common complete execution
meaning. The [common-protocol profile](common-protocols.md) composes these local
calls with messages and shared protocol bodies; participant projection is separate.

The maintained implementations are
[`LocatedExecution`](../../../../formal/Zkc/Source/LocatedExecution.lean) and
[`ControlAgreement`](../../../../formal/Zkc/Source/ControlAgreement.lean).

## Local calls and admission

Let `Role` be a type with decidable equality. Each role has its own state and
event types, `State role` and `Event role`; they need not be the same at every
participant. The joint observer's state is the family `role -> State role`.
This family is not a runtime input exposed to every participant.

A located call fixes the actual definition table, callee reference, primitive
interpretation, ordered argument values and local handler. It runs the stored
body using only `states role`. The handler and primitive interpretation are
fixed independently of this joint-state argument. Argument availability and
the legitimacy of any captured provider state remain admission obligations.

This reference treats the selected local call as one ordered joint step. Its
body may perform several local effects, but peers do not interleave inside that
step. A finer schedule or a larger atomic block needs its own correspondence;
state separation alone does not justify changing these boundaries.

Definition typing alone does not establish a local algorithm. A selected effect
classification `locations : Interface.Op -> Option Role` assigns admitted local
effects to their role. `none` excludes ordinary peer communication and effects
without a local contract. `LocallyAdmitted` instantiates the existing
`Conforms` judgment with this policy for the actual interpreted body. It covers
all interface-typed replies, including effects in stored callees and subsequent
branches. `reached_local` proves every reached interface call has that role's
classification. The existing phase-admission framework can supply such
conformance; this profile adds no second summary checker.

Classification is a supplied interface contract. Its correctness for a physical
handler, service or foreign call needs the corresponding realization law.
Admitted local effects do not automatically establish confidentiality, resource
issuance or a sampling law. An oracle/service extension must provide its own
local execution and schedule contract.

For example, the whole Sumcheck verifier source includes a receive operation.
Storing it as a shared definition preserves its meaning; it does not turn it
into a local computation block. The maintained negative control proves that
every positive-round invocation fails the local policy when message reception
is classified as communication. Such a body belongs to a protocol or supplied
endpoint until communication is represented explicitly at the common boundary.

## Complete result and origin

The joint reference attaches an origin with the fields:

```text
role, entry, selected instance, invocation/iteration path, local site.
```

Path frames distinguish a child invocation from an indexed loop iteration.
The enclosing structured traversal must produce these values. Resolution must
connect the declared instance identity to the actual definition and contracts.
The origin record itself proves neither connection and is not a transcript
encoding, artifact hash, unforgeable identity or persistent symbol format.

Given a local execution `(outcome, final, events)`, lifting it:

- retains the same outcome;
- replaces only the executing role's state with `final`;
- tags every local event with the selected origin;
- records that origin on a stop, including a stop with no events.

The joint observer therefore knows which located boundary stopped. It does not
infer the precise internal operation of an uninstrumented local body, fabricate
a rejection at another role, or deliver cancellation to a peer.

`run_frame` preserves every other role's state. `run_local` proves that changing
peer state cannot change the action's outcome, own post-state, stopped origin or
events, for the same explicit inputs, interpretation and handler. This is a
local factorization result; it does not prove privacy of the joint observation.

Sequencing uses the existing `Execution.follow`. `run_stopped` proves that a
stopped local call retains its effects, actual state and origin without running
the normal suffix. The executor must use that complete outcome. Calling the
reference function again manually is not a justified resume operation.

Local state separation does not permit arbitrary reordering. Moving another
role's effect before a stopping action can change both the event prefix and
that role's final state. Complete-execution preservation remains the obligation.

## Actual agreement for shared control

Fix a declared list of participants and separately bound values
`values : Role -> Option A`, with decidable equality on `A`.
`ControlAgreement.check` returns the common actual value or one of:

```text
noParticipants
unavailable(role)
disagreement(role).
```

It never treats a missing guard as `false` or a missing loop count as zero.
The theorem `check_ok_iff` states exactly:

```text
check(participants, values) = ok(value)
  iff participants is nonempty
      and every declared role is bound to some(value).
```

The list's order selects the first reported failure. Repetition of a role adds
no agreement fact; uniqueness and validity of the entry's role roster are
separate formation requirements. An undeclared role receives no agreement
guarantee.

For Boolean guards, `branch_denote` connects an accepted choice to the actual
typed `Region.branch` at a declared role, under an explicit binding equality
for that condition and environment. The same check applies to natural loop
counts; it does not generate loop projections or infer a public complexity bound.

This is validation of an agreement premise for the selected reference. It is
not a new verifier rejection rule, an automatically inserted consensus check,
or a message that informs a participant. A native implementation may establish
agreement through admitted inputs or explicit delivery with its own law. It must
not silently add communication or disclose private choices to implement this
reference check. Private local branching and the permitted merging of identical
uninformed continuations remain distinct cases.

## Evidence and compiler obligations

[Located-call controls](../../../../formal/Tests/LocatedCalls.lean) use three roles
with different state types, reuse one stored body under role-local handlers,
retain failed draw and duplicate-use state, and distinguish iteration/instance
origins. They include a stopped action with an empty trace, a call-reordering
counterexample, missing/divergent guards and counts, and actual branch denotation.
[Sumcheck controls](../../../../formal/Tests/SumcheckDefinitions.lean) retain the
whole-source communication obstruction for arbitrary positive round counts.

The maintained common-protocol subset supplies role-tagged input/result
ports, typed instance references, traversal-derived paths, independently received
values, shared calls and fixed public loops. Portable source formation, role
remapping and global choice remain open. Projection must construct the
corresponding local bodies and establish the selected agreement, effects and
complete-outcome contracts. These local laws do not prove that larger theorem
or a native scheduler, transport, backend or cryptographic implementation.
