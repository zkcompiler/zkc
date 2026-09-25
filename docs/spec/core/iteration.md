# Iteration over finite bodies

The [finite execution kernel](execution.md) gives meaning to each step. An outer
controller can run an unbounded number of such steps; it is not itself an
endpoint with a finite public call bound. Outer iteration retains the finite kernel,
its stop reasons, phase laws and observers unchanged.

## Steps and prefixes

For controller state `C` and final result `A`, fix:

```text
body : C → Proc Σ (C + A)
```

`inl next` requests another step; `inr value` finishes. A terminal `Stop` remains
terminal. Retrying a recoverable condition therefore uses returned data, never
catches a `halt`. A native compiler supplies inspectable stored bodies and their
admission, rather than treating an arbitrary host callback as compiled source.

The finite approximation is:

```text
approximate body 0     c = done (inl c)
approximate body (n+1) c = bind (body c) fun answer =>
  match answer with
  | inl next => approximate body n next
  | inr a    => done (inr a)

evaluate body h n c s = run h (approximate body n c) s
```

An approximation returns a complete result: outcome, actual state and events.
A returned continuation is *pending*, not exhausted or rejected. The prefix law
equates evaluation at `n+m` with evaluation at `n` followed by resumption for
`m`, using the actual successor state and concatenating events. Completed or
stopped prefixes are stable under further fuel; any two completed prefixes
agree. A deterministic total handler diverges under this controller exactly
when every finite prefix remains pending. This retains each finite observation;
it does not assume a normalized discrete distribution on infinite streams.

`evaluateM` interprets the same finite approximation using the selected monadic
handler. Its resumption law follows from ordinary monadic sequencing and retains
the actual residual state and events when the monad produces an execution.
Pure handlers recover `evaluate` exactly. A probability model still establishes
the actual reached joint law, normalization and conditional bounds; an outer
exception may produce no execution record and is not an inner terminal stop.
State carried by an outer monad such as `StateT` also survives the monadic
resumption law. It is not stored in `Execution`: saving that record alone does
not preserve the outer state or justify restarting the monad from its initial
state.

The approximation index bounds controller steps. If every body reached along
any typed reply has an all-reply call bound `k`, the `n`-step approximation has
bound `n*k`. Equivalently, a preserved all-reply invariant may admit those
continuations and exclude unreachable seeds. Reachability under one selected
handler is insufficient. Arithmetic
work, event storage, native integer capacity and provider progress need separate
contracts. An arbitrary callback's totality or finite cost is not checked by
this mathematical definition.

## Admission and preservation

A continuation invariant relates `C` to the actual interaction phase. Every
admitted body conforms at that phase and returns either a continuation satisfying
the invariant at its exit phase or a final value satisfying the terminal
postcondition. Those premises give conformance and return admission for every
prefix. They do not establish eventual production or cryptographic completeness.

Operation interpretation commutes with approximation. Complete per-step
simulation, under the chosen residual-state and event relations, lifts through
every prefix. These laws reuse ordinary `bind` and `follow`; no rollback or
exception-catching rule is added. Other claims can use weaker relations such as
[acceptance and exposed-output correspondence](../realization/representations.md).

Represented controllers may have different continuation and final value types.
A state-dependent continuation relation is interpreted in the actual residual
states. Each related pair of steps preserves the continue/finish tag, that
continuation relation or the final value relation, the state relation, exact
stops and the selected observations. These premises lift to every equal-length
prefix and its explicit deployment closure. They also allow a continuation
invariant to exclude unreachable input values. An all-reply call bound need hold
only for invariant-admitted continuations, provided every returning branch
preserves the invariant at its exit phase.

Grouping `width` bodies into one step satisfies
`approximate (approximate body width) blocks = approximate body (blocks * width)`.
The same numerical cap on grouped and ungrouped steps generally differs in
meaning. This finite grouping law is not arbitrary weak/stuttering simulation;
unequal or data-dependent progress needs a separate correspondence and policy.

## Deployment policy

For a selected finite deployment cap, `close` maps only `returned (inl c)` to
`stopped exhausted`, maps `returned (inr a)` to `returned a`, and retains a
previous stop. State and events remain unchanged. Exhaustion is a policy result;
it is not evidence that the unbounded reference cannot later succeed.
After closure, policy exhaustion and a body's own `exhausted` stop have the same
terminal tag. Pending-versus-stopped probability accounting therefore uses the
unclosed prefix, including the `pending` mass in `accepted_lower_bound`.

A service claiming persistent iteration transfers actual successor resource
handles across steps. Fresh initialization of a backend is a different service,
even if its successful outputs are compatible. Attempt-local resource retirement
revokes that resource without restoring consumed randomness or reusing identity.
Authoritative counters remain the counters of the actual completed prefix.
Facts depending on a retired capability require invalidation; unrelated facts
still need their ordinary validity premises.

The fixed-body resumption law assumes the complete semantic state is retained.
A native mutable callback can hide relevant state in its captures; that state
must survive resumption and participate in the realization relation. Resetting
such captures between calls changes the service even when the explicit `S` is
preserved. Callback panic, divergence or effects outside the supplied execution
record are not automatically modeled as a terminal `Stop`.

## Publication

An attempt buffers its tentative proof payload. A successful terminal result may
feed a separate publication action, with its own failure contract. Discarded
attempts emit no proof-publication event. This is a premise about the attempt's
actual effects, not a consequence of using a sum return type. Audit events,
consumed randomness, quotas and already external effects remain observable under
the selected observer.

`observeEvents` is append-preserving; a later discard marker cannot erase an
earlier published payload. A construction needing speculative output must buffer
it before publication. Failed publication can leave a produced proof unpublished
and must be included in any [completeness bound](../properties/probability.md).

## Scope

This model covers finite retries, iterative search and segmented services. It
does not supply distributed knowledge of a later choice, general asynchronous
delivery, recursive stored source, fairness, interruptions within one atomic
handler call, or a measure on infinite interactive traces. Those require their
own transition and observation laws. The
[design rationale](../../rationale/finite-bodies-under-iteration.md) states when
a broader recursive calculus would be warranted.
