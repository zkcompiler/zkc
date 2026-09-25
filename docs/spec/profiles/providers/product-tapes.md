# Product tapes and next requests

This profile gives a finite source next-coordinate access to a hidden product
tape. Its correspondence relates a retained tape to online sampling together
with reconstruction of the actual unused suffix. The next-request law uses
the complete reached checkpoint, before the next coordinate is delivered.

## Interface and product initialization

Let `D` be the provider value type, `J` a local signature, and
`localH : MonadHandler PMF J S E` a normalized local handler. Fix a
[distribution](../../properties/probability.md#normalized-discrete-distributions)
`q : PMF D`. Neither `D` nor local state `S` needs to be finite. The extended
signature and event type are:

```text
Op       = draw | local(o : J.Op)
Reply(draw)     = D
Reply(local o)  = J.Reply(o)
Event    = draw(d : D) | local(e : E).
```

The local handler receives only `S`. It may change that state, emit events,
sample local randomness or stop. It has no argument giving it the provider
suffix. Source continuations can depend on previously delivered replies.

Define the normalized finite product distribution and state expansion:

```text
tape(q,0)   = pure []
tape(q,n+1) = q >>= (d ↦ tape(q,n) >>= (rest ↦ pure (d::rest)))
expand(q,(s,n)) = tape(q,n) >>= (rest ↦ pure (s,rest)).
```

Every list in the support of `tape(q,n)` has length `n`. Coordinates are
independent with the same fixed law `q`; this definition is stronger than
equality of their marginal distributions.

An initialized experiment may first sample `(s,n)` from any normalized joint
law `init : PMF (S × Nat)` and choose a source from that same sampled pair.
It then expands the suffix using the equation above. Thus local setup and
length can be correlated, while the suffix conditional on them has the fixed
product law. A source or local handler selected using hidden future coordinates
does not have this initialization meaning.

## Persistent and online handlers

The persistent state is `(s : S, rest : List D)`. Its transitions are:

```text
persistent(draw,(s,[])) =
  pure (stopped exhausted, (s,[]), [])
persistent(draw,(s,d::rest)) =
  pure (returned d, (s,rest), [draw(d)])
persistent(local o,(s,rest)) =
  localH(o,s) >>= ((out,t,es) ↦
    pure (out,(t,rest),map local es)).
```

The online state replaces the suffix by its remaining length:

```text
online(draw,(s,0)) = pure (stopped exhausted,(s,0),[])
online(draw,(s,n+1)) = q >>= (d ↦ pure (returned d,(s,n),[draw(d)]))
online(local o,(s,n)) =
  localH(o,s) >>= ((out,t,es) ↦ pure (out,(t,n),map local es)).
```

Both retain a local handler's actual stopped outcome, post-state and events.
A local failure does not consume the suffix or execute a later draw. An
exhausted draw emits no new event; preceding draw/local events survive through
common sequencing. A zero-coordinate tape is a valid initial state.

Embedding a local source replaces each local operation by `local(o)` and
otherwise preserves its control. Executing that embedding retains the suffix
unchanged, maps its emitted events through `local`, and preserves the whole
local result, including a stop.

## Complete residual reconstruction

For `r = (out,(s,n),es)`, define:

```text
expandResult(q,r) =
  tape(q,n) >>= (rest ↦ pure (out,(s,rest),es)).
```

For every well-founded reply-adaptive body `p`, actual local handler and initial
online state `st`, the complete execution distributions satisfy:

```text
expand(q,st) >>= (actual ↦ runM persistent p actual)
  = runM online p st >>= (r ↦ expandResult(q,r)).
```

This is equality of complete results with concrete residual tapes after
expansion. It includes successful returns, explicit halts, exhaustion and
local failures. It does not claim equality between a particular fixed tape
and a newly sampled tape in an individual deterministic execution.

For a draw, the law separates a product head from its tail. For a local call,
it exchanges independent local sampling and suffix sampling. Repeated use
through the well-founded body establishes the displayed law without a bound on
arithmetic work or a uniform bound over an unrelated source family. Sampling
`init` and choosing `p(st)` first gives the same equality under joint
initialization.

Define the checkpoint of a concrete result by:

```text
checkpoint(out,(s,rest),es) = (out,(s,length(rest)),es).
```

Applying it after `expandResult(q,r)` yields `r` with probability one. Applying
it to persistent execution yields exactly the online execution distribution.
It retains the complete local state and previous outcome/events, but exposes
no unused suffix values. This is a mathematical information boundary; treating
the whole checkpoint as a public release requires the selected release policy.

## Actual next-request decision

Let `View = Execution (S × Nat) Event A`, and let `active : View → Bool` be
fixed before the next draw. For an actual checkpoint `v`, define:

```text
request(active,v) =
  match v.outcome with
  | stopped why → halt why
  | returned _  → if active(v) then call draw done else halt abort

requesting(active,v) =
  match v.outcome with
  | stopped _  → false
  | returned _ → active(v) and (v.remaining ≠ 0).
```

Here `v.remaining` is the length component of `v.state`. `requesting` selects
fibers with a possible returned draw. An active zero-length request still
calls the provider and stops exhausted. A declined request stops abort without
a call; a prior outer stop retains its reason.

The joint observation executes the next request at the actual persistent
post-state:

```text
nextJoint(q,localH,p,st,active) =
  expand(q,st) >>= (initial ↦ runM persistent p initial) >>=
  (actual ↦
    let v=checkpoint(actual)
    runM persistent (request(active,v)) actual.state >>=
    (next ↦ pure (v,next.outcome))).
```

The selected result is `(checkpoint, next outcome)`. It omits the next
operation's post-state and events; those still have their complete operational
meaning. A claim about them uses complete execution, rather than equating this
projection with the entire run. Previously emitted events occur inside `v`
and are not emitted again by `request`.

Let `ν = runM online p st`. Residual reconstruction gives the exact alternative
of sampling `v` from `ν`, running the same request under the online handler
at `v.state`, and returning `(v,next.outcome)`. Hence:

```text
nextJoint(v,returned d) =
  ν(v) * (if requesting(active,v) then q(d) else 0).
```

For `ν(v)>0` and `requesting(active,v)=true`, division by `ν(v)` gives `q(d)`.
For `ε : ℝ≥0∞`, if `q(d)≤ε` for all `d`, the returned joint mass is at most
`ε*ν(v)` on every fiber. Stopped and declined fibers remain in the normalized joint law; they
are not conditioned away. Selecting an event after seeing `d` gives a different
conditional law.

*Example (informative).* A source that draws twice from `[7]` stops exhausted
with an empty suffix and the earlier `draw(7)` event. A source that draws once
and aborts from `[7,9]` retains suffix `[9]`. Neither result permits restarting
the original two-coordinate distribution as its residual provider.
