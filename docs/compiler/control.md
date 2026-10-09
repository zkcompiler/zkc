# Control and completion

Ordered local algorithms use typed calls, conditionals, alternatives and finite
state-carrying loops. [Local control](../spec/ir/control.md),
[variants](../spec/ir/variants.md) and [completion](../spec/ir/completion.md)
own their exact formation, resource and failure rules.

## Branches and loops

A conditional executes one branch. All branches must form correctly and agree
on continuing result types. Explicit captures are evaluated once. Affine captures
are consumed once on branch entry and checked within each branch; reusable loop
invariants and affine carried state occupy different ports.

A finite loop reads its bounds once. Zero trips return initial state. The
`local.condition` terminator yields a continue flag and carried values: false
returns the state from the reached trial and skips remaining iterations.

```text
state = local.for(index = lower .. upper, state):
    state, found = trial(state)
    local.condition(not found, state)
```

Isolated regions and explicit block arguments expose capture and backedge maps
to MLIR. Helper expansion recurses without unrolling loops or executing both
arms. Physical conversions and releases stay in their actual control region.
The Runner uses managed frames and cleans up on every outcome. A future SCF
lowering would need to preserve these index, custody, failure and work contracts.

## Participant completion

`protocol.finish_if` takes an owner-local condition and the complete entry result
tuple. True returns from that participant, including through nested repeats.
False yields fresh SSA successors for consumed affine members; copyable values
keep their ordinary names. A component containing this action cannot be applied,
because inlining must not change which entry it completes.

```text
rng, challenge = draw(rng)
send(compute(challenge))
rng = finish_if(unsuitable(challenge), false, rng)
rng, second = draw(rng)
send(compute(second))
return(true, rng)
```

The reached prefix and actual successors survive early completion. Skipped
yields, suffixes and iterations do not execute. Constructed transcripts retain
the current state at every exit, including exits inside event-free loops.

Returning is independent of retry policy. The [attempt Host](../runtime/attempts.md)
reads an explicitly selected completion Boolean; malformed messages, backend
failures and exhausted budgets remain fatal. A producer return alone does not
establish that its candidate proof validates.

In joint execution, peers continue after one participant returns. Communication
with a returned peer reports `ReturnedEarly`; all participants returning with
no pending packet reports `Completed`. These Host outcomes are distinct from
application acceptance and from the attempt completion Boolean.

## Resource identity and limits

[Resource-origin analysis](resource-origins.md) checks continuing affine roots
through local branches, calls and repeats. Equal roots do not mean equal states,
equal samples or permission to clone a capability. Private variant tags retain
their separate history restrictions.

This profile admits bounded local algorithms. General dynamic protocol choice,
unbounded execution and arbitrary references or closures require additional
contracts. A local algorithm cannot invent communication to obtain a remote
value. [Native validation](../../tests/native.md) covers control, custody, cleanup and
retained-prefix failures; native Lean correspondence remains open.
