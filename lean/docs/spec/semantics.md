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

`RawProgram.denote` evaluates the raw grammar directly, using operand lookup and
the selected primitive interpretation without invoking typed elaboration.
`denote_elaborate` proves that every successful elaboration preserves the open
process on all inputs. Static admission examines dormant branches and empty-loop
bodies even though direct execution examines only reached code.

`Source.OperationExpansion` replaces an operation with a typed source body
whose arguments are exactly its declared operands. Its local equation lifts
through source captures, branches and loops. One pass expands original sites
once; it does not recursively unfold a cyclic helper dictionary.
`Source.Normalizer.check` elaborates both actual raw bodies and compares their
normalized erasures. `check_sound` proves equality of their open processes on
every input. Each normalizer needs a semantic preservation proof; normalizers
compose. Refusal means that this sufficient criterion did not establish equality.

`Algebra.RingNormalization` supplies a separate executable criterion for pure
ring expressions: distribute multiplication, move signs into coefficients, and
compare unordered sums of unordered products. Checked integer-coefficient
identities hold in every commutative ring. The criterion does not collect like
terms, move effects, remove guards or equate different provider meanings.

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

## Interpretation, provider state and observations

`Proc.interpret` replaces each source operation with a reply-preserving lower
process. `run_interpret` and `runM_interpret` equate staged execution with
execution under the composed handler, including inner stops, residual states
and ordered events. The monadic equation requires a lawful monad. It does not
establish total probability mass or recover execution records discarded by an
outer exception. `runM_interpret_expand` combines this equation with the existing
`runM_expand` law; its premise is the selected providers' local distributional
state equation, not an assumed whole-program correspondence.

`Related` compares terminal outcomes, a stated residual-state relation and two
selected event views. Its existing sequencing and observer laws require that
continuations and final-state observers respect that relation. Equal acceptance
alone is insufficient: a later session can distinguish different caches even
when both earlier sessions accepted. Contexts obtain operation replies; the
hidden handler state is not an additional attacker argument.

`Realization.ExecutionSimulation` additionally requires coverage of every input
in the claimed implementation domain by an admitted specification input. Its
initial and residual-state relations are separate. `compose` retains an admitted
intermediate input and an actual intermediate residual state. `transport` carries
predicates of the complete selected observation only when final-state observers
respect the residual relation. `ofHandlers` derives whole-process simulation from
per-operation laws and coverage. These laws do not supply a probability coupling,
resource restriction, input decoder or adversary correspondence.

`Provider.run_joint_related` lifts component simulations through adaptive clients
of a sum signature with a pair of disjoint state cells. Both components retain
their actual successor state on stops. This construction does not justify
splitting a shared cache or assert probabilistic independence. `related_coarsen`
permits postprocessing an established event view. It cannot strengthen the view
to expose hidden events, cache contents or timing/cost counters. Such observations
need their own compatible state/event relation.

`Provider.cached` is a deterministic finite-supply memoizing model. A miss consumes
the next supplied value and stores it at that key; a hit preserves state and
returns the stored value. A miss with no supply stops with `exhausted`. Every
entered query emits its key, including hits and exhausted misses. `cached_repeat`
proves successful repeated-key consistency, and `cached_preserves_other` proves
other entries survive. This model supplies no sampling, uniformity, independence,
cryptographic encoding or concrete-provider theorem.

## Operation-sensitive cost

`Cost.handler` instruments a deterministic handler with a natural-number ledger.
Its `Charge` function receives the operation, input provider state and complete
operation result. It charges every entered operation, including one that stops;
it cannot inspect or alter the prior ledger. `run_eq` proves exact preservation of
the original outcome, events and provider state, with only the accumulated charge
added to the ledger. The ledger is not automatically an attacker observation.

`spent_bind` charges the actual continuation at the actual residual state on
return, and zero continuation cost on a terminal stop. `expansionCharge` measures
the actual lower process implementing a source operation. `Cost.run_interpret`
proves equality of complete instrumented executions under staging and composition.
Thus one logical operation can incur several lower queries, or stop after a
partial expansion, without losing its residual state or prefix charges.

`spent_interpret_le` transports operation-specific cost upper bounds, and
`spent_interpret_bound` combines local expansion bounds with existing `Within`
call bounds. No second call-bound predicate is introduced. `queryCharge` counts
all cache queries, while `missCharge` counts attempted absent-key accesses,
including exhausted misses; neither is automatically native work, permutation
calls or running time. Consumers select and justify the theorem's cost model,
including any attacker pre-queries and final verifier completion calls.

## Runtime-selected finite control

`Zkc.Source.FiniteControl.Loop` retains one environment-dependent bound selector
and one indexed body. Selection evaluates the bounds once. Its denotation enters
successive indices in `[lower, upper)`, carries each returned value forward and
performs no body calls when `upper ≤ lower`. `admitRange` checks both bound
magnitudes against an explicit maximum, including inverted intervals.

`iterateFrom_add` proves exact sequential interval splitting, including early
stops. `iterateFrom_congr` proves that only in-range body meanings can affect
execution. Index-insensitive bodies equal `repeatN`, and `denote_region_iterate`
connects their continued denotation to existing `Region.iterate`. Selected-count
call bounds reuse `Within`; indexed phase invariants reuse `Boundary.Returns`
and its sequencing admission laws.

`iterateWhile` supports bounded conditional completion: each entered body returns
either `Step.continue` or `Step.finish`. Finishing returns the carried value to the
surrounding continuation, while a `Proc.halt` terminates it and preserves the actual
stopped state/events. Exhausting the selected count returns the current value;
zero trips do not evaluate a condition. The call bound is at most the selected
count times the uniform body-call bound. These are independent model laws, not
native bound checking, instruction/frame accounting, frontend elaboration or a
common-source export extension.

Bounds and completion flags are not implicitly public or secret. Selecting them
from private data can leak through the executed event prefix or the cost ledger
even when both runs return the same Boolean. A security consumer must state the
attacker's permitted observations and prove compatibility with its chosen view;
boundedness alone supplies no noninterference claim.

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
