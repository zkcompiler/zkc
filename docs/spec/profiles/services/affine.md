# Affine services and captured source

The affine service retains one setup and authenticated input across repeated
requests. The controller selects partial or complete delivery using its permitted
history. Captured source fixes that controller and its inputs before invocation.

## Affine setup and response values

Let `F` be a commutative ring. Write `Triple F = F × F × F`, with coordinates
`x,y,z`. A witness is `(x,y)` together with the equation `x*y=1`. A setup is:

```text
Setup F = { delta : F, kx : F, ky : F, kz : F, star : F }.
```

All setup values may be verifier-chosen. In particular, `delta` may be zero.
For witness `w`, input-mask triple `r` and publication triple `p`, define:

```text
publications(w,r) = (w.x-r.x, w.y-r.y, 1-r.z)
tags(s,r) = (s.kx-s.delta*r.x, s.ky-s.delta*r.y, s.kz-s.delta*r.z)
keys(s,p) = (s.kx+s.delta*p.x, s.ky+s.delta*p.y, s.kz+s.delta*p.z)

coefficients(w,m) = (m.x*m.y, w.x*m.y+w.y*m.x-m.z)
byPrefix(s,w,p) = coefficients(w,tags(s,publications(w,p)))
gate(s,p) = keys(s,p).x*keys(s,p).y - keys(s,p).z*s.delta

localResponse(a,mask,chi) = (chi*a.0+mask.0, chi*a.1+mask.1).
```

Pairs use coordinates `0,1`. The publication map is its own inverse at fixed
witness, so `publications(w,p)` recovers the input masks for that witness and
publication. The witness equation gives:

```text
gate(s,p) = byPrefix(s,w,p).0 + byPrefix(s,w,p).1*s.delta
tags(s,publications(w,p)).z = keys(s,p).z-s.delta.
```

The prover coefficient computation receives witness values and tags, without
the verifier keys as additional arguments. This is an explicit mathematical
input boundary, not a native authentication mechanism.

A response mask drawn from one coordinate `r : F` is
`(star-delta*r,r)`. The additive map `L(u,v)=u+delta*v` sends it to `star`.
The map `r ↦ (star-delta*r,r)` is a bijection onto that fiber, with inverse
the second coordinate, including at `delta=0`. A uniform coordinate therefore
gives a uniform fiber mask when `F` is finite. Arbitrary coordinate laws retain
their actual induced distribution and need not be uniform on that fiber.

## Requests, delivery and history

The repeated-service request and permitted history are:

```text
Request F = { star : F, challenge : F, cutAfterU : Bool }
Event F = response(request : Request F, u : F,
                   v : Option F, tag : Option F)
        | stopped
History F = { events : List (Event F), halted : Bool }
empty = ([],false)
Controller F = Triple F → History F → Option (Request F).
```

The request's `star` selects that response's affine fiber; it can differ from
the setup's initial `star` without modifying the persistent setup. For fixed
setup, witness and publication, the response computation is:

```text
a = byPrefix(s,w,p)
actualResponse(req,r) =
  localResponse(a,(req.star-s.delta*r,r),req.challenge)
outputTag = tags(s,publications(w,p)).z.
```

The operation signature has `request(req)` and `stop`. Reply types are:

```text
Reply(request req) = if req.cutAfterU then F else F × F × F
Reply(stop) = Unit.
```

Delivery for a response pair `(u,v)` returns only `u` when the cut is true,
and `(u,v,outputTag)` otherwise. Its recorded event is respectively
`response(req,u,none,none)` or `response(req,u,some v,some outputTag)`.
Writing this event as `event(req,reply)`, define:

```text
receive(h,req,reply) = (h.events ++ [event(req,reply)], false).
```

Only the returned shape is available to the controller. The request, including
its cut, is chosen before delivery. The controller cannot choose the cut after
reading the current undelivered second component. Exposing a callback between
components requires a different operation boundary. Partial delivery itself
does not halt the service; the next request may use its delivered `u`.

## Controller source and complete execution

For a fixed controller, publication `p`, public horizon `n` and history `h`,
the source is:

```text
source(0,h) = done h
source(n+1,h) =
  if h.halted then done h else
  match controller(p,h) with
  | none → call stop (_ ↦ done (h.events ++ [stopped],true))
  | some req → call (request req) (reply ↦ source(n,receive(h,req,reply))).
```

The interaction's phases are `(remaining : Nat, history : History F)`.
All calls are owned by the requester; the responder supplies their replies.
A call is enabled exactly when the remaining horizon is positive and the
history is not halted. A returned stop sets phase `(0,(events++[stopped],true))`.
A returned request decreases the horizon by one and records its actual typed
reply. Every shape-valid request/reply is allowed; honest arithmetic is not
an admission premise. The source conforms from `(n,h)` and has call bound `n`
for every typed-reply path. Returning at horizon zero does not imply that the
history is halted or that a proof has been accepted.

The actual handler state is `(history, tape : List F)`. It uses the fixed
setup, witness and publication:

```text
stop at (h,tape):
  let next=(h.events ++ [stopped],true)
  (returned (), (next,tape), [stopped])

request(req) at (h,[]):
  (stopped exhausted, (h,[]), [])

request(req) at (h,r::rest):
  let reply=deliver(req.cutAfterU,actualResponse(req,r),outputTag)
  (returned reply, (receive(h,req,reply),rest), [event(req,reply)]).
```

A delivered partial response consumes one coordinate just as a full
response does. Controller stop consumes none. Exhaustion preserves the
preceding history and emits no new response or service-stop event. It is an
outer stop, distinct from a returned halted history. For every body run by
this handler:

```text
finalState.history.events = initialHistory.events ++ execution.events.
```

The controller source starts with the same history as the handler state.
Under its actual returned replies, the source's carried history tracks that
state. Complete execution retains unconsumed tape and all prior emissions,
including on exhaustion.

## Checked controller expressions

The selected controller language uses the common
[ring expressions](../source/expressions.md#expression-syntax-and-meaning). Its four
expressions are `stop`, `star`, `challenge` and `cut`. It binds natural input
indices to these values:

| Index | Value |
|---|---|
| 0, 1, 2 | Publication coordinates `p.x,p.y,p.z` |
| 3 | The natural length of `h.events`, cast into `F` |
| 4 | The `u` of the last event if it is a response; otherwise zero |
| 5 | `s.delta` |
| 6 | `w.x` |
| 7 | `byPrefix(s,w,p).0` |
| 8 and above | Zero in the total reference environment |

Let `scope=[0,1,2,3,4,5]`, and let `check(scope,e)` mean that every syntactic
dependency of `e` lies in `scope`. The exact selected predicate is:

```text
Good(c) ⇔ check(scope,c.stop) ∧ check(scope,c.star)
        ∧ check(scope,c.challenge) ∧ check(scope,c.cut).
```

It checks all expressions and both arms of every expression conditional.
Unavailable current-response inputs, hidden witness/cache inputs and even
syntactically cancelling hidden reads are rejected. Total zero semantics for
index eight does not make that input permitted.

With decidable equality in `F`, denotation at the displayed environment `env`
is:

```text
denote(c,s,w)(p,h) =
  if eval env c.stop = 0 then none else
    some (eval env c.star, eval env c.challenge, decide(eval env c.cut ≠ 0)).
```

A zero stop-expression value means stop; a nonzero cut-expression value means
deliver only `u`. The field cast of a history length can wrap or identify
different natural lengths. The public horizon, not this cast or a particular
guard expression, bounds execution.

For fixed `c,s` with `Good(c)`, the denoted controller is equal for any two
valid witnesses at the same publication and history. The proof uses agreement
on the six admitted slots. It does not equate controllers generated from
different witness-dependent code. The expression fragment exposes only the
listed history projection; an arbitrary mathematical controller may inspect
the entire supplied history, under its own same-controller premise.

## Joint service coupling and its observer

For the same setup and controller, define the simulated response and tag:

```text
simulatedResponse(p,req,z) =
  (req.challenge*gate(s,p)+req.star-z*s.delta,z)
simulatedTag(p) = keys(s,p).z-s.delta.
```

For the real coordinate `r`, choose
`z=r+req.challenge*byPrefix(s,w,p).1`. The actual and simulated response pairs
are then equal, as are their output tags. Translation of the coordinate is
a bijection; no division by `delta` or nonzero-delta premise is used.

For the finite-horizon reference, define `step(h,r)` to leave a halted history
unchanged, append `stopped` and mark halted when the controller returns none,
or append the selected response event otherwise. The real step uses the actual
response; the simulated step uses the displayed simulated response. Define:

```text
fold(0,h,()) = h
fold(n+1,h,(r,tail)) = fold(n,step(h,r),tail).
```

At each history the coin translation is identity if halted or if the controller
stops; otherwise it is the response translation above. The full tape bijection
changes the head first, computes the same simulated next history, and recursively
changes the tail from that history. Thus later translations can depend on
earlier delivered responses, including partial responses, without consulting
future coordinates. Prefix translation maps the input-mask triple to
`publications(w,r)`. Combining the prefix and adaptive tape bijections gives:

```text
real(s,w,controller,n,coins)
  = simulated(s,controller,n,wholeCoins(s,w,controller,n,coins)),
```

where each result is `(publication, final history)` and
`coins : Triple F × Tape F n`. The typed tape has one coordinate per horizon
step. This reference fold traverses its fixed horizon after a history halts;
those later steps are identities on history. The operational source returns
immediately and retains the actual unconsumed suffix. Their established
connection identifies history, not those different consumption descriptions.

For a finite ring with decidable equality, sample `Triple F × Tape F n`
uniformly. The bijection preserves that uniform law, so every joint
publication/history output has the same probability under real and simulated
execution. The simulator is independent of the witness; the same setup and
controller therefore give equal joint masses across valid witnesses.
A bijection without a sampling-law correspondence does not establish this
probability equality for a biased or correlated tape.

The actual common-execution observer is:

```text
view = (publication, execution.outcome : Outcome (History F)).
```

Starting from empty history and the full `n`-coordinate tape gives a returned
history equal to the reference fold. This supplies the observer connection for
the finite uniform experiment. Complete deterministic runs also support short
or extra tapes, but this experiment does not establish a distributional theorem
for arbitrary exhaustion schedules. The observer excludes hidden setup,
witness, coefficient cache and residual tape. Postprocessing that same observer
preserves its equality; releasing additional state needs a new relation.

## Immutable coefficient preparation

The reusable value is `byPrefix(s,w,p)`. A valid coefficient cache binds the
same setup, witness and publication to exactly that pair. Its producer uses
the expressions `input[2]*input[3]` and
`input[0]*input[3]+input[1]*input[2]-input[4]`, with ordered inputs
`[w.x,w.y,m.x,m.y,m.z]` for the actual tags `m`.
These prover inputs are distinct from the controller's index meanings.

One realization substitutes a proved-valid pair into the response handler.
The handler is then exactly equal to direct recomputation for every body and
state, including exhaustion. A stateful realization retains
`(history,tape,cache : Triple F → Option (F×F))` and relates it to the reference
state by equal history, equal tape and
`ValidCache(byPrefix(s,w),cache)`. A nonempty request acquires the value at
the actual publication before computing its response. Stop and exhaustion
leave this cache unchanged; exhaustion performs no acquisition.

This relation is preserved for every reply-adaptive client. It preserves the
whole outcome, visible events and residual provider tape, while allowing
different private coefficient storage. The corresponding transformation rule
retains the typed source and its ordinary lowering and selects this handler
realization under equal source environments and the stated initial relation.
It does not permit an arbitrary edited candidate.

Only immutable coefficients are shared. Each delivered request still consumes
its actual coordinate and constructs its own mask and response. Equality of
coefficients gives no permission to reuse a response or sample. A changed
setup or witness changes the cache provider and requires the common
[cache-validity and rebinding law](../../core/contracts.md).

## Literal selection and issuance

Let an external expression environment be `env : Nat → Option F` and its
permitted scope be a list of indices. A literal contains fixed service code
`Program` as above and fixed [local causal code](../sumcheck/local-prover.md#local-prover-state-and-code).
The finite selection tree is:

```text
Tree = leaf(literal, captures : List (Expr Nat))
     | ifz(guard : Expr Nat, yes : Tree, no : Tree)

LiteralOK(literal,n) ⇔ Good(literal.service) ∧ 5≤n
                   ∧ ∀ i ∈ codeInputs(literal.causal), i<n

deps(leaf(lit,es)) = concat(map exprDeps es)
deps(ifz(e,p,q)) = exprDeps(e) ++ deps(p) ++ deps(q)
valid(leaf(lit,es)) = LiteralOK(lit,length(es))
valid(ifz(e,p,q)) = valid(p) ∧ valid(q).
```

The five-capture requirement is this service's setup arity. It is not a
minimum for standalone local code. Extra captures are allowed and are checked
and retained. Literal code contains no host callback that can generate code
from an unbound hidden input.

`select(env,tree)` follows zero-test guards and at the selected leaf returns
that literal with every capture expression evaluated in the same environment.
Its total evaluator uses zero for an unavailable value. Issuance first checks
that every dependency of the whole tree is both permitted and present, using
the common [whole-capture readiness](../source/expressions.md#whole-capture-readiness):

```text
issue(scope,env,tree) =
  if ready(scope,env,deps(tree)) and valid(tree)
  then some(select(env,tree)) else none.

Issued F = { code : Literal, inputs : List F }.
```

This checks dormant leaves, guards and captures before selection. Consequently
successful issuance never depends on the unavailable-input fallback. Its
causal input occurrences are in range of the retained vector. At invocation,
setup is that vector's first five values in order
`[delta,kx,ky,kz,star]`; the causal code receives the same entire vector.
Total projection uses zero for absent entries on an arbitrary forged `Issued`
value, while checked issuance establishes the stronger five-present-values
condition. Invocation uses retained values, not a reread of the external world.

For the same tree, agreement on the permitted environment preserves the whole
issuance result, including refusal, selected literal and actual capture values.
Successful agreement therefore gives the same setup and a `Good` service
controller, discharging the same-controller premise of the joint service law.
Checking only that two possibly different programs are each `Good` would not
give this result. Witness-dependent setup or source publication needs its own
agreement or joint-release proof.

## Installed source environment

Role-qualified admission interprets the actual ordered input bindings using
the common [input view](../../language/inputs.md), sets scope to
`[0,…,bindingCount-1]`, and calls the same issuer. A successful result proves
that each tree dependency names an actual permitted slot with an available
value. Same permitted role views give the same result, including refusal.

For installation request `r`, use the actual
[reserved-name installation](../compiler/factor-preparation.md#reserved-name-installation)
result `out=execute(capacity,r,world)`. Define the local source environment by:

```text
localEnv(namespace,out.world)(i) =
  if addr(namespace,i) ∈ out.world.known
  then some(out.world.values.challenge(addr(namespace,i)))
  else none.
```

Presence is distinct from a value equal to zero. Under a successful patch,
each `i<length(r.captured)` yields exactly `r.captured[i]`. The role world
exposes that local environment only under the designated actor's owned slots,
has no shared slots, and retains the supplied hidden component without reading
it. The binding list is the actor-owned indices of the captured vector.

```text
installAdmit(actor,capacity,r,tree,world,hidden) =
  if out.success then
    admit(actor,installedBindings(actor,length(r.captured)),
          installedWorld(actor,r.namespace,out.world,hidden),tree)
  else none.
```

On installation success, this equals issuance from `localEnv` with scope
restricted to those captured indices. On installation failure, it is `none`,
even if old namespace entries would allow the raw issuer to succeed. After a
successful patch, old entries outside it cannot influence selection. For the
same request, capacity and tree, the guarded result is independent of the prior
outer world; successful issuance fixes the actual captured setup and controller.
This statement concerns the returned `Option Issued`. Installation's changed
world and events remain those of its separate state-module contract, including
failure framing. Neither installation nor issuance failure invokes the source.
No source-level role tag authenticates a native namespace request by itself.
