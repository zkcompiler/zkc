# Scalar rounds

This profile specifies coefficient messages, logical interaction and a supplied
round adapter. Its normal result is a residual scalar. The
[complete verifier](interactive.md#complete-verifier-source) adds the terminal check.

## Messages and logical rounds

A message is an ordered triple of coefficients:

```text
Message F = { constant : F, linear : F, quadratic : F }
evaluate(m,r) = m.constant + (m.linear*r + m.quadratic*(r*r))
boundary(m) = evaluate(m,0) + evaluate(m,1).
```

These definitions use a semiring. Decidable equality is required for executable
checks. Every triple of field values is a legal interface payload; legality
does not assume `boundary(m)=claim`, an honest prover equation, or a vanishing
quadratic coefficient. A serialized adapter establishes its actual domain and
payload correspondence separately. This profile does not select the auxiliary
[natural-word message frontend](../README.md#message-shape-reference-client)
as its wire format.

The logical signature has calls `message : Message F`, `challenge : F`, and
`reject : Unit`. For a public remaining count `k` and current claim `s`, define:

```text
rounds(0,s) = done s
rounds(k+1,s) = call message (m ↦
  if boundary(m)=s then
    call challenge (r ↦ rounds(k,evaluate(m,r)))
  else call reject (_ ↦ halt reject)).
```

A rejecting boundary invokes no challenge. The rejection notification is an
operation before the explicit stop; if an arbitrary handler stops during that
operation, its actual stopped result is retained by common sequencing.

The roles are `prover` and `verifier`. Message calls belong to the prover;
challenge and reject calls belong to the verifier. The phases are:

```text
message(k,s) | challenge(k,m) | reject | finished
start(0,s)   = finished
start(k+1,s) = message(k,s).
```

The only enabled phase/call pairs are matching message, challenge and reject.
A returned message moves to `challenge(k,m)` if its boundary matches, and to
`reject` otherwise. A returned challenge moves to `start(k,evaluate(m,r))`.
The total phase-advance function gives `finished` on other pairs; those pairs
remain disallowed except the enabled reject, whose returned reply also gives
`finished`. A stopping operation does not advance the phase.

`rounds(k,s)` conforms from `start(k,s)`, has logical call bound `2*k`, and
every returned path ends in `finished`. It returns a residual scalar, not a
terminal verifier decision. Its structured source has sorts `scalar`, `message`,
`boolean`, `unit`, pure `check(message,scalar)` and `evaluate(message,scalar)`
operations, and effectful receive/draw/reject operations. Public iteration of
the round body, carrying the scalar and then returning it, denotes exactly
`rounds`.

## Supplied early-round adapter

The early-round adapter uses a commutative ring with decidable equality, a
triple message `(a,b,c)`, a round record `(a,b,c,r)`, and a supplied mathematical
function `evalRound : Round F → F`. Its boundary is `((a+a)+b)+c`.
The standard function is `(a+b*r)+c*(r*r)`. An arbitrary supplied `evalRound`
also determines the scalar update in this adapter's source and phase rules.

Its endpoints are:

```text
send  : S → (F × F × F) × S
react : S → F → S
draw  : Q → F × Q.
```

Message handling calls `send` on prover memory, retains its successor memory
and emits the message. Challenge handling calls `draw` on provider state,
updates prover memory with the delivered challenge using `react`, and emits
that challenge. Rejection handling returns unit with unchanged state and a
reject event. No endpoint receives the other endpoint's hidden state through
this interface. Realizing these restrictions in a native callback requires
its actual correspondence; they assert no sampling independence by themselves.

At count zero the adapter returns the scalar with unchanged endpoint states
and no events. At a positive count it sends, checks, and either rejects with
the post-send prover state and unchanged provider state, or draws and continues
with the actual post-draw states and `evalRound`. This is exactly the logical
source under the supplied handler. Its call bound is `2*k`, including rejected
paths. The early adapter's `draw` is total; the [complete verifier's tape provider](interactive.md#interactive-execution-and-failure) has an explicit exhausted outcome.

Executing all scheduled draws and later replaying the checks can preserve a
verdict while changing rejected-run provider state and events. That deferred
schedule is not complete-execution equality with this early adapter. Scalar
return still needs the enclosing relation and actual terminal consumer.
