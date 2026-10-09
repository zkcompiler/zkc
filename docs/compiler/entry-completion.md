# Entry completion and bounded search

The [conditional completion profile](../spec/profiles/compiler/entry-completion.md)
owns the semantics. Conditional completion supports returning from an entry
before its suffix and ending a bounded local search before its remaining trials.
They use the existing mathematical, participant, exec and physical stages and the
shared interpreter.

## Chosen structure

`protocol.finish_if` is an ordered owner-local action. It takes a condition and
that owner's complete entry result tuple. Its false path returns only the affine
members under fresh SSA names; true completes the participant immediately.
This makes resource consumption explicit without a new attempt region, exception
kind or implicit resource lookup. Copyable values retain their ordinary names.
A component containing this action cannot be applied: inlining must not change
which entry a return completes. Future component-local returns need their own
scope contract.

```text
rng, challenge = draw(rng)
message = compute(challenge)
send(message)                         // reached prefix is retained
retry = unsuitable(challenge)
rng = finish_if(retry, false, rng)    // false is the host completion result
rng, second = draw(rng)               // skipped when retry is true
send(compute(second))
return(true, rng)
```

Returning is independent of retry policy. The attempt host reads its configured
Boolean completion port and authenticates the actual RNG successor. A failed
backend hook, malformed message or exhausted budget remains fatal. An early exit
inside nested repeats transfers the actual entry tuple through each active frame,
without executing a skipped yield or iteration. Current transcript state follows
the same path, including otherwise event-free loops.

`local.for` keeps its finite bound, carried values and captures. The terminator
`local.condition` explicitly yields a continue flag followed by those values.
This uses ordinary SSA uses and MLIR region interfaces. It avoids a second loop
operation with otherwise identical structure and avoids charging unused trials
merely to carry a found bit. Its executable `for_while` tag makes the changed
termination behavior explicit to independent readers.

```text
state = local.for(index = lower .. upper, state):
    state, found = trial(state)
    local.condition(not found, state)
```

A zero-trip loop returns its initial state. A false condition still returns the
state from the reached trial. It completes this local loop only.

## Execution and checking

- `ProgramState::ReturnIf` exposes the conditional-return boundary. The explicit
  `return_if` method validates origin/site, charges the instruction, then evaluates
  the condition. `advance_local_control` uses it for independent execution.
- Constructed proof checking validates the current transcript on every early
  exit and its continuing successor. A partial challenge/observation pair cannot
  contain a completion. An incomplete returned proof prefix is not accepted by
  the independent validator.
- Joint execution skips a returned participant's suffix while peers continue.
  Live communication with a returned peer produces `ReturnedEarly`; all roles
  completing with no pending packet produces `Completed`. These host outcomes
  remain distinct from application completion data.
- Attempt and joint reports retain the reached return coordinate. Successful
  outputs are published only after required retention and custody cleanup.
- [Language](../language/mathematical.md) exposes completion under its source
  rules. Native Lean execution correspondence remains open.

## Maintained evidence

[Runtime controls](../../crates/zkc-runtime/src/interactive/control_tests.rs)
exercise flat/nested exits, continuing affine values, wrong control coordinates,
unknown tags and malformed records, empty/early-ending local loops, iteration budgets,
and injected failures at every returned frame and root result retention.

[Native attempts](../../compiler/test/native_attempts.py) and their
[execution client](../../crates/zkc-tools/examples/native_attempts.rs) exercise
both constructed transcript suites in ordinary, unsimplified and storage-release
modes. Eventful and event-free nested exits preserve prefix observations and
consumed randomness. The next completed proof matches a direct execution with
the advanced random tape; independent validation refuses truncated prefixes.

[Authored transcript clients](../../compiler/test/native_authored_transcripts.py)
exercise early Monero prefix return and bounded OpenVM search with exact proof
payload and retained primitive-work checks. The
[joint generator](../../compiler/test/native_entry_completion.py) and
[execution client](../../crates/zkc-tools/examples/native_entry_completion.rs)
exercise flat, loop and nested schedules with either, both or neither participant
returning, including communication inside loops. Three-role controls check live
role count agreement after a peer returns and distinct owner-local result values.
Owner/signature/component, continuation and source/candidate mutations check
admission and construction boundaries.

Independent formal models do not interpret the native `return_if` and
`for_while` records. Their source/control theorems establish no native connection.
One-shot proof production reports `return_at` and returns proof bytes without
an attempt history;
use the attempt report for retained retry decisions and prefixes. A producer
return alone does not establish that the resulting proof will validate.

These are bounded implementation checks. They do not prove a retry probability
bound, Fiat–Shamir soundness, upstream compatibility or universal protocol support.
[Structured relation binding](relation-bindings.md), domain/key composition and
[bulk mathematical capacity](mathematical-composition.md) have composed
clients. The [setup generator](../../compiler/test/native_setups.py) also checks
conditional completion after the first of two setup-backed applications under a
derived transcript, in ordinary, unsimplified and storage-release modes. Both
participants return the current state; the skipped setup still requires entry
authorization. A distinct second evaluation point also exercises the false
completion branch through both setups and final return. Further native work is recorded in the [roadmap](../roadmap.md).
