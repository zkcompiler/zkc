# PIR semantics

## Mathematical and participant layers

A `Language` has sorts and typed operations. A mathematical `Meaning` assigns a
Lean type to each sort and an interpretation to every operation. Group operations
can be interpreted in a module over a field; different native nominal domains
must not be silently equated. The scalar proof-request profile checks domain
assignments explicitly because its chosen field/group interpretation is uniform.
The native provider implementing those domains is a separate obligation.

A source context indexes the type of every reference. Elaboration constructs a
well-typed program or refuses it. Values available to participants are optional:
absence is not zero, false, or a default group element. Inputs carry role scopes;
projection preserves restrictions, sender/receiver actions and service ownership.
Inputs shared by two roles may have different role-local values. The semantic
model never derives agreement merely from their shared source port name.

## Effects and observations

`PIR.Proc` is a well-founded interaction tree with returned values, terminal stops and
typed requests whose continuations consume actual replies. A handler maps an
operation and state to its outcome, successor state and ordered events. `run`
threads that state. `runM` does the same in a lawful monad, enabling VCVio
probabilistic handlers. Rejection, refusal, incompleteness and a returned false
Boolean remain distinct. A statement annotation has no runtime proof effect.

`ExactRefinement p q` contains equality of their open processes. Its laws preserve
all handlers, replies, stops, final states and events, and compose under bind.
This is intentionally stronger than final-result agreement. It can reject an
optimization that changes observable actions even when outputs coincide. Such a
case needs a separately stated observation/refinement interface and proof.

## Observation budgets and unbounded behavior

`Machine` has explicit configurations, internal steps, requests and terminal
outcomes. `runFrom` returns a prefix whose progress is running or finished.
A zero/exhausted observation budget does not become protocol rejection. Resuming
for budgets `m` and `n` equals running for `m+n`; terminal states are stable and
prior events remain a prefix. A spin control stays running at every budget.

A `Proc` embeds in this machine. `complete_run` relates every observed
prefix to the full finite execution. `eventually_finishes` proves that every
fixed total handler reaches the same complete result at some finite budget.
It does not assert a uniform depth across all reply-dependent continuations or
a finite number of branches when the reply type is infinite.
The current scalar exporter admits finite straight-line bodies with bounded
static helper inlining. It does not export general native loops or recursion.
A partial external-reply/waiting scheduler is not supplied by the total-handler
model; it requires a separately specified interface.

## Adequacy boundary

Successful typed admission proves facts about the imported constructors. The
native exporter and JSON-to-constructor renderer are independently tested,
reviewed boundaries. The C++ reference interprets retained SSA directly; Lean
interprets the exported program. Differential comparisons cover requests,
replies, states, results and stop prefixes over Z/97. This detects discrepancies
in the admitted profile, not a universal compiler correctness theorem or a
production group/sampling implementation proof.
