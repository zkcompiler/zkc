# Execution

An execution records a computation's outcome, residual state and ordered events.
The definitions below describe one mathematical interpretation at fixed public
parameters. They use the [common notation](../conventions.md#mathematical-notation).

## Signatures

An operation signature `Σ` consists of:

```text
Op    : Type
Reply : Op → Type
```

An operation value contains its actual interpreted arguments and references.
For `op : Σ.Op`, its reply type is `Σ.Reply op`. Neither operation values nor
reply domains are assumed finite.

## Outcomes

For a result type `A`, outcomes and terminal stop reasons are:

```text
Stop      = reject | abort | exhausted | incomplete | refused
Outcome A = returned(a : A) | stopped(reason : Stop)
```

| Reason | Meaning at the enclosing execution boundary |
|---|---|
| `reject` | Terminal rejection |
| `abort` | Explicit interruption |
| `exhausted` | Terminal resource or provider exhaustion |
| `incomplete` | A bounded runner does not complete the requested body |
| `refused` | A dynamic execution request is refused |

The constructors are distinct. Preserving an outcome preserves its stop reason.
This type is not a diagnostic or wire format; the applicable reply and event
contracts specify required detail and subject bindings.

A recoverable error is returned data, such as a value of `Except Error Value`.
It invokes the body's continuation. A terminal stop does not. The enclosing
boundary determines which meaning applies to a local error.

Admission errors occur before execution and have the meaning specified by the
[checking judgment](../verification/judgments.md#failure-boundaries).
A dynamic guard can separately produce `stopped refused`. Returning a value
does not imply verifier acceptance; the applicable
[terminal predicate](../properties/relations.md#soundness-direction-reduction) determines
acceptance. A retained verifier result and a later continuation result are
[separate records](../profiles/services/accepted-continuations.md#verifier-decisions-and-ordinary-composition).

## Bodies

For a signature `Σ` and result type `A`, a body has the inductive form:

```text
Proc Σ A = done(a : A)
         | halt(reason : Stop)
         | call(op : Σ.Op, next : Σ.Reply op → Proc Σ A)
```

`done` returns a value. `halt` stops explicitly. `call` requests an operation
and continues with its actual returned reply. The continuation is a total
mathematical function and can choose later arguments and branches from that
reply. It has no implicit argument exposing handler state.

`Proc` is a well-founded tree. Reply branching can be infinite; a uniform
natural-number bound on all paths is a separate condition. This denotation is
not a portable grammar or permission to serialize host-language closures.
An actual source supplies its [input and capture contract](../profiles/source/named-inputs.md#exact-ordered-binding).

## Complete results

Let `S` be the state type and `E` the event type. A complete result and a
deterministic handler have types:

```text
Execution S E A = {
  outcome : Outcome A,
  state   : S,
  events  : List E
}

Handler Σ S E = (op : Σ.Op) → S → Execution S E (Σ.Reply op)
```

Tuple notation `(out, s, es)` abbreviates the three fields in that order.
`state` is the actual residual state, including when `outcome` is stopped.
`events` is the sequence emitted by that execution, in emission order.
The interpretation specifies which events represent communication, internal
work or resource use.

## Sequencing

For result types `A` and `B`, let `k : A → S → Execution S E B`. The function
`follow` sequences a complete result with `k`:

```text
follow((stopped r, s, es), k) =
  (stopped r, s, es)

follow((returned a, s, es), k) =
  let (out, t, fs) = k a s
  (out, t, es ++ fs)
```

A stopped prefix preserves its reason, state and events and skips `k`.
A returned prefix supplies its value and actual residual state to `k`.
The final outcome and state come from that continuation; events retain the
prefix followed by the continuation's events, including if the continuation
stops.

*Example.* Let `x : Execution Nat Nat Bool` be `(returned true, 1, [7])` and
let `k : Bool → Nat → Execution Nat Nat Unit` satisfy
`k a s = (stopped abort, s + 1, [8])`.
Then `follow(x,k) = (stopped abort, 2, [7,8])`. The earlier returned value does
not replace the final stop. If the first outcome is instead `stopped exhausted`,
sequencing retains state `1` and events `[7]` and never invokes `k`.

## Deterministic interpretation

For `h : Handler Σ S E`, interpretation is defined by recursion on the body:

```text
run h (done a)   s = (returned a, s, [])
run h (halt r)   s = (stopped r, s, [])
run h (call o k) s = follow(h o s, fun a t => run h (k a) t)
```

Each reached call applies the handler exactly once, including a call that stops.
Sequencing introduces no rollback, resource refund, allocation release or event
erasure. An operation that promises a transaction establishes its own
failure-state contract. Cleanup after a stop requires explicit enclosing
semantics because an ordinary suffix is skipped.

## Body composition

For `p : Proc Σ A` and `k : A → Proc Σ B`, substitution at returned leaves is:

```text
bind (done a)   k = k a
bind (halt r)   k = halt r
bind (call o f) k = call o (fun reply => bind (f reply) k)
```

For `x : Execution S E A`, `f : A → S → Execution S E B` and
`g : B → S → Execution S E C`, sequencing satisfies the derived law:

```text
follow(follow(x,f),g) = follow(x, fun a s => follow(f a s,g))
```

Interpretation preserves body composition:

```text
run h (bind p k) s = follow(run h p s, fun a t => run h (k a) t)
```

Consequently, if `run h p s = run h q s`, then the same suffix `k` satisfies:

```text
run h (bind p k) s = run h (bind q k) s
```

This premise compares complete results at the stated initial state. Equality of
returned values alone is insufficient. The law does not change the handler,
initial state or bindings, and associativity preserves the order of calls.

## Call boundary

A call is atomic relative to the interpreter's controller: no body-continuation
step occurs between events emitted by one handler invocation. An invocation
can emit several ordered events. A controller that reacts between those events
requires a finer operation boundary or a correspondence with a finer execution
model.

Mathematical handlers return complete results. Native termination, timeouts,
internal cost and persistence outside the result record require their own
contracts. The [execution envelope](../conventions.md#execution-envelope)
states the scope of the selected model.

## Uniform call bounds

For `n : Nat` and `p : Proc Σ A`, `Within n p` is defined by:

```text
Within n     (done a)   = True
Within n     (halt r)   = True
Within 0     (call o k) = False
Within (n+1) (call o k) = ∀ reply : Σ.Reply o, Within n (k reply)
```

A publicly bounded endpoint supplies this predicate at its declared public
bound. The quantifier includes every declared reply, including dishonest
payloads. The bound counts reached handler invocations, including the stopping
invocation. It does not count emitted events, argument computation or work
inside a handler. A cryptographic-query bound requires a correspondence between
the queries and these invocations.

*Example.* Suppose an operation returns a natural number `m`, after which a
body makes exactly `m` further calls. Every path is finite. Nevertheless, no
fixed natural number bounds the initial call and all possible returned lengths.
Well-foundedness therefore does not discharge `Within` at a public bound.

## Actual-call records

Let `P` be an [interaction](../language/interaction.md#roles-and-phases) over
`Σ`, and `h : Handler Σ S E`. Instrumentation uses state `P.Phase × S` and
events `(P.Phase × Σ.Op) + E`. Define:

```text
recordCalls P h op (phase,s) =
  let (out,t,es) = h op s
  let phase' = match out with
    | returned a => P.advance phase op a
    | stopped r  => phase
  (out, (phase',t), inl(phase,op) :: map inr es)
```

The left injection records the phase and operation of the actual invocation;
the right injection retains the handler's events. A stopping call records its
input phase and actual residual state without fabricating a reply transition.

For an instrumented result `x`, let `eraseCalls x` retain its outcome, second
state component and right-injected events, removing left-injected records.
Let `calls x` be its left-injected records in order. The following laws hold:

```text
eraseCalls(run (recordCalls P h) p (phase,s)) = run h p s

Conforms P p phase ⇒
  ∀ (before,op) ∈ calls(run (recordCalls P h) p (phase,s)),
    P.enabled before op

Within n p ⇒ length(calls(run (recordCalls P h) p (phase,s))) ≤ n
```

Here [conformance](../language/interaction.md#all-reply-conformance)
is the all-reply interaction predicate. Erasure requires neither conformance nor
a bound. The permission and count conclusions require their respective
premises independently; neither requires honest replies or successful
completion. Instrumentation itself performs no admission check.

## Persistent history

For `log : S → List E`, suppose every `op : Σ.Op` and `s : S` satisfies:

```text
log (h op s).state = log s ++ (h op s).events
```

Then every body and initial state satisfies:

```text
log (run h p s).state = log s ++ (run h p s).events
```

Both the premise and conclusion include stopped results. Without this step
law, an event sequence does not establish what history is available to a later
state-reading action.

## Outer effects

Let `M : Type → Type` be a monad with `pure : A → M A` and sequencing
`(>>=) : M A → (A → M B) → M B`. A handler in `M` has type:

```text
MonadHandler M Σ S E = (op : Σ.Op) → S → M (Execution S E (Σ.Reply op))
```

For `k : A → S → M (Execution S E B)`, sequencing inside `M` is:

```text
followM((stopped r,s,es),k) = pure (stopped r,s,es)
followM((returned a,s,es),k) =
  k a s >>= fun (out,t,fs) => pure (out,t,es ++ fs)

runM h (done a)   s = pure (returned a,s,[])
runM h (halt r)   s = pure (stopped r,s,[])
runM h (call o k) s = h o s >>= fun x =>
  followM(x, fun a t => runM h (k a) t)
```

Retention concerns an `Execution` produced inside `M`. An outer exception that
produces no execution record supplies no residual-state or event report through
this interface. Inspectable failure is represented inside the record or through
an explicit adapter for that outer effect.

For a lawful monad, where `pure` and `>>=` satisfy left identity, right identity
and associativity, the derived laws are:

```text
runM h (bind p k) s = runM h p s >>= fun x =>
  followM(x, fun a t => runM h (k a) t)

runM (fun op s => pure (h op s)) p s = pure (run h p s)
```

For monads `M` and `N`, a lift `lift : M A → N A` at every result type that
preserves `pure` and `>>=` satisfies:

```text
lift(runM h p s) = runM (fun op s => lift(h op s)) p s
```

A monad need not be a distribution carrier. A probabilistic interpretation
supplies its [complete execution distribution and joint laws](../properties/probability.md#normalized-discrete-distributions).
Discarding stopped mass and renormalizing defines a conditional experiment;
it does not preserve the original execution law.

## Iterated finite execution

[Iteration](iteration.md) defines coherent prefixes of an outer controller whose
steps use this kernel. Pending continuation, completed execution and actual
budget exhaustion remain distinct. It changes neither `Proc` nor `follow`.
