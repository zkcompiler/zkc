# Typed Sumcheck framing

This construction uses the [logical calls and phases](scalar-rounds.md#messages-and-logical-rounds),
[ordered coefficients](quadratic.md#ordered-coefficient-encoding), and
[complete verifier](interactive.md#complete-verifier-source). It retains the actual
statement root and each attempted query in its complete execution.

Fix a commutative semiring `F` with decidable equality and a polynomial dimension
`n`. The prover callbacks `send` and `react` have the
[interactive interface](interactive.md#interactive-execution-and-failure).

## Typed framing and construction phases

The construction signature distinguishes `receive`, `absorb(message)`,
`sample`, `squeeze` and `reject`. Receive returns a message; sample and squeeze
return a field value; absorption and rejection return unit. Its frames are
typed logical values:

```text
Frame F = context(domain : String, rounds : Nat, claim : F)
        | statement(schema : String, values : List F)
        | message(round : Nat, value : Message F)
        | request(round : Nat)
        | challenge(round : Nat, value : F).
```

The ordered execution events are `message(m)`, `challenge(r)`, `query(frames)`
and `reject`. Absorption changes retained framing state without emitting an
additional execution event. Define provider interfaces:

```text
Draw F Q  = Q → Outcome F × Q
Query F Q = List (Frame F) → Q → Outcome F × Q.
```

The fresh expansion maps the three logical calls to receive, sample and
reject respectively. Its interaction uses the logical phases and enables
only those corresponding calls; other calls are disabled. Its handler returns
`stopped refused` without state change or events on absorb or squeeze.

The framed expansion instead maps a logical message call to receive followed
by absorption of that exact returned message, a challenge call to squeeze,
and rejection to reject. Its construction phase is:

```text
FramedPhase = ready(logicalPhase) | pending(logicalPhase,expectedMessage).
```

In `ready`, receive/squeeze/reject are enabled exactly when the corresponding
logical call is enabled. A returned receive enters `pending` with its actual
message. In `pending`, only absorption of that same message is enabled;
its returned unit advances the logical message phase and reenters `ready`.
Returned squeeze and reject advance their logical phases and stay `ready`.
Other total advance cases leave the construction phase unchanged, without
making those calls legal. Sample is disabled in the framed interaction.

These expansions preserve the logical admission and returning-phase contracts.
Fresh expansion has at most one construction call per logical call; framed
expansion has at most two. The logical `2*count` bound therefore gives bounds
`2*count` and `4*count` respectively. The latter is a sufficient expansion
bound, not a claim of exact work or optimal counting.

## Complete statement root and framed execution

For fixed `F,n`, the full Sumcheck root is:

```text
root(domain,p,claim) =
  [context(domain,n,claim),
   statement("sumcheck.quadratic.v1",coefficients(p))].
```

The state is `(prover : S, provider : Q, frames : List (Frame F), position : Nat)`.
Initialization uses the actual root above and position zero. Equality of roots
at fixed `F,n` implies equality of domain strings, initial claims and coefficient
objects. The root contains the entire ordered coefficient list; a provider
receiving it can inspect that list. The selected field interpretation and any
confidentiality claim retain their [binding](../../realization/artifacts.md) and
[joint disclosure](../../properties/disclosure.md) obligations. Logical root
injectivity does not define cross-field byte identity or hide coefficients.

The framed handler uses the same supplied `send` and `react`, with the actual
`query : Query F Q`. Its transitions are:

| Call | Result, retained state and ordered events |
|---|---|
| `receive` | Call `send(prover)`, update prover memory, return the actual message and emit `message(m)` |
| `absorb(m)` | Append `message(position,m)` to frames; return unit with no events |
| `reject` | Return unit with unchanged state and emit `reject` |
| `sample` | Stop `refused` with unchanged state and no events |

Squeeze has the following complete transition. First set
`request = frames ++ [request(position)]` and invoke `query(request,provider)`.
For its actual reply `(out,nextProvider)`:

```text
out = stopped why:
  return (stopped why,
          (prover,nextProvider,request,position),
          [query(request)])

out = returned r:
  return (returned r,
          (react(prover,r),nextProvider,
           request ++ [challenge(position,r)],position+1),
          [query(request),challenge(r)]).
```

The complete framed entry runs the same typed verifier, with framed operation
expansion, initial accumulator `(claim,[])`, and the root bound to the actual
polynomial. A received message is absorbed before its arithmetic boundary is
checked. Consequently a failed boundary retains the message frame and post-send
memory, emits message then rejection, and makes no provider query. A stopping
query retains its attempted request and successor provider state without
advancing the position or calling `react`.

An independent recursive description sends and absorbs each message, checks
the boundary, and then either stops or performs the displayed query transition
and recurses with the updated accumulator. At count zero it returns the
accumulator unchanged. Sequencing that recursion with the actual pure terminal
function equals the complete framed entry, including all stopped results.
Replacing evaluation with the checked child also preserves this entire run.

Every final frame sequence extends the same initial root. Every actual query
event also has that root as its prefix, including a query whose provider stops.
Successful queries append the request and challenge at the current position
before advancing it. These are state/event invariants of the actual handler,
not an assumption that an independently constructed transcript matches the run.

The earlier scalar-round framed component initializes only
`[context(domain,count,claim)]` and returns a residual scalar. It lacks the full
polynomial root and terminal check and is not this complete entry. Neither
entry identifies its arbitrary query provider with independent uniform draws.
Byte-codec injectivity, cryptographic statement binding, oracle access, sampling
and Fiat–Shamir security require their selected construction and experiment
laws. The typed framing equations do not supply them.
