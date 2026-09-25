# Finite commitment sessions

This profile interprets two atomic commitment sessions with shared preparation.
A finite scheduler observes their global protocol trace; cancellation and failed
opening are returned state and data.

## Finite commitment-session machine

The separate commitment-session client uses two session identifiers,
`SessionId = Bool`. Its value types and provider are:

```text
Phase = fresh | committed(c : Nat) | done | cancelled | failed
Command = commit | reveal | open(message : Nat, coin : Nat) | cancel
Action = { sid : SessionId, command : Command }
Message = commitment(Nat) | opening(Nat,Nat) | accept | reject | cancel | invalid
Event = SessionId × Message
Input = { key : Nat, message : Nat, coin : Nat }

Provider T = {
  prepare : Nat → T,
  commit  : Nat → T → Nat → Nat → Nat,
  verify  : Nat → Nat → Nat → Nat → Bool
}.
```

The ordered commitment arguments are key, prepared value, message and coin;
verification arguments are key, commitment, message and coin. A provider
declares concrete total functions. No cryptographic binding, hiding or
honest-opening law is implicit in this record.

For input `i`, let `make(m,r)=provider.commit(i.key,table,m,r)` and
`check(c,m,r)=provider.verify(i.key,c,m,r)`. The local transition is:

| Phase and command | Next phase | Ordered messages |
|---|---|---|
| `fresh`, `commit` | `committed(make(i.message,i.coin))` | The resulting commitment |
| `committed(c)`, `reveal` | `done` if `check(c,i.message,i.coin)`, else `failed` | Actual stored opening, then accept or reject |
| `committed(c)`, `open(m,r)` | `done` if `check(c,m,r)`, else `failed` | Supplied opening, then accept or reject |
| `fresh` or `committed(c)`, `cancel` | `cancelled` | Cancel |
| Every other pair | Unchanged | Invalid |

Only a fresh commit needs preparation. State is
`(sessions : SessionId → Phase, cache : Nat → Option T, trace : List Event,
builds : Nat)`, initially both sessions fresh with empty cache/trace and zero
builds. Direct acquisition computes `prepare(key)`, leaves the cache unchanged
and increments builds by one. Shared acquisition uses a hit at zero builds,
or computes and inserts the value at one build. Validity requires every cached
value at a key to equal that provider's `prepare(key)`.

An action reads the actual input and phase for its session, acquires only if
needed, applies the displayed transition, changes only that session's phase,
appends all messages tagged with that session, and adds the acquisition count.
Cancellation, invalid attempts and failed openings remain returned state/data.
They do not cause an outer process stop.

## Adaptive scheduling and preparation source

A scheduler is `List Event → Option Action`. It sees the ordered global
protocol trace. Its finite execution is:

```text
adaptive(0,s) = s
adaptive(n+1,s) =
  match scheduler(s.trace) with
  | none → s
  | some action → adaptive(n,step(s,action)).
```

Scheduling occurs after the complete action, including both opening and
verdict messages. Those emissions create no intermediate scheduler call.
For direct and shared execution, the relation is equality of all session
phases and the global trace, together with validity of both caches. It
preserves every finite adaptive schedule from related states. Final caches
and build counters may differ. A scheduler that reads those quantities needs
a different relation. Independent local phase updates do not justify swapping
their ordered global messages.

The selected preparation realization uses the
[natural table interpreter](../compiler/factor-preparation.md#concrete-table-preparation).
For key `h`, its preparation key has version `1`, origin `700`, captures `[0]`,
and six instructions: instruction `i`, for `i=0,…,5`, appends
`(register[i]+h) % 7`. The result contains seven cells. Consumption is
`(m+table[r % 7]) % 7`, with the interpreter's total missing-cell fallback;
verification compares `c` with `(m+h*(r % 7)) % 7`. The concrete table and
consumption correspondence controls use `h,m,r : Fin 7`. This finite additive
group client has explicit opening collisions and claims no cryptographic
commitment security.

Lowering a fresh commit requests exactly that preparation key, computes its
transition from the returned table, emits its ordered protocol messages, and
continues with the resulting session state. Other actions emit their transition
messages without preparation. Adaptive lowering queries the scheduler on the
returned source trace after each action. This defines one finite preparation
program, interpreted in either direct or memo mode under the common handler.

The source returns the state of the direct reference machine at the actual
interpreted provider. Its internal `builds` field is reference bookkeeping,
even in memo mode. Actual work, savings and overhead are the handler's events.
The separate source law connects both projections:

```text
execution.outcome = returned(referenceFinalState)
initialState.trace ++ observe(execution.events) = referenceFinalState.trace.
```

Here `observe` keeps only ordered protocol emissions, using the common
preparation projection. The handler starts with an empty valid preparation
cache. Result/trace equality holds in both modes for the same finite source;
the event-derived price comparison is
`memoWork+memoOverhead≤directWork` exactly when `memoOverhead≤memoSaved`.
This condition is separate from the logical build-counter bound. Prepared
tables may be shared; session messages and supplied coins are not cached or
resampled by this source. A probabilistic enclosing commitment experiment
must supply their actual joint initialization law.
