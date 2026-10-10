# Executable vector service

An independent consumer of the existing typed source and direct-plan semantics,
with request-dependent replies and a model-specific executable interface.

| Module | Responsibility |
|---|---|
| `Language` | Count/vector/predicate sorts, dependent interface replies and complete deterministic handler |
| `Format` | Closed descriptors, canonical field entries and named invocation/state codecs |
| `Tools.VectorService` | Existing source/candidate checking and an independent executable reference |

`request n` calls an interface whose successful reply is a list of `Fin 7` with
length `n`. `send n` returns the propositionally constrained Boolean `n = 0`.
`sum` computes the sum of a vector's natural representatives. Thus a reply can
determine a later request's length while the source retains an ordinary vector
sort. `request_and_send` performs both calls inside one source operation and
returns only the final Boolean; its intermediate vector still has a dependent
reply type. Request lengths above 1024 stop with `refused` before a provider call.

The handler consumes one supplied seed per external call. A vector repeats that
seed; a send returns the required Boolean. Every attempted call increments the
state counter and emits its request event, even when the tape is empty and the
call stops with `exhausted`. All example declarations enter the maintained audit.

From `lean/`, with the pinned dependencies prepared:

```sh
lake build vector-service
.lake/build/bin/vector-service check SOURCE PLAN
.lake/build/bin/vector-service run SOURCE PLAN INPUTS
```

The input record is `[namedInputs, [callCount, seedTape]]`. Counts use natural
numbers; seeds are canonical values below seven. Both finite tree source and
compact regions use the maintained generic artifact checker. This example adds
no phase policy, cryptographic security claim or native correctness theorem.

The [typed language](Language.lean) fixes the representation and provider laws.
A native provider needs a separate connection to these laws. A Lean typed
reply cannot contain a malformed value merely to reproduce a host error as a
logical stop.
