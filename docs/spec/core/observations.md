# Observations

An observation selects information from an
[execution](execution.md#complete-results). The selection is an operand of the
claim being made. It is fixed independently of the execution outcome being
compared.

## Event projections

For event type `E` and observation type `O`, let `view : E → List O`. Define:

```text
observeEvents view es = flatMap view es
```

The projection can erase an event, preserve it, or expand it into several
observations. It retains order and satisfies:

```text
observeEvents view (xs ++ ys) =
  observeEvents view xs ++ observeEvents view ys
```

An event list is not automatically public, persistent controller memory or a
protocol transcript. Each such interpretation specifies its own contract.

## Execution relation

Let `S` and `T` be state types, `E` and `F` event types, `A` a common result type
and `O` a common observation type. Fix:

```text
R     : S → T → Prop
left  : E → List O
right : F → List O
```

For `x : Execution S E A` and `y : Execution T F A`, define:

```text
Related R left right x y :=
  x.outcome = y.outcome ∧
  R x.state y.state ∧
  observeEvents left x.events = observeEvents right y.events
```

The relation preserves exact outcomes, including stop reasons, and relates the
actual final states on both returning and stopping executions. `R` need not be
an equivalence relation. When logical and represented results have different
types, the applicable [representation relation](../realization/representations.md#related-complete-results)
specifies how their returned values correspond in those final states.

*Example.* Two executions can both return `()` and emit `[7]` while leaving
states `1` and `2`. Their values and events agree, but a suffix that returns the
current state distinguishes them. Trace agreement alone does not supply the
state premise needed for composition.

## Sequential composition

Let `x` and `y` be as above, with `Related R left right x y`. For a result type
`B`, let:

```text
f : A → S → Execution S E B
g : A → T → Execution T F B
```

If the suffixes satisfy:

```text
∀ a s t, R s t → Related R left right (f a s) (g a t),
```

then [sequencing](execution.md#sequencing) satisfies:

```text
Related R left right (follow(x,f)) (follow(y,g)).
```

The common returned value and actual related residual states supply the suffix
premise. Stopped prefixes invoke neither suffix and retain their related
results.

## Handler replacement

For a common signature `Σ`, let `h : Handler Σ S E` and
`g : Handler Σ T F`. Define:

```text
HandlerRelated R left right h g :=
  ∀ op s t, R s t → Related R left right (h op s) (g op t)
```

For every `p : Proc Σ A`, `s : S` and `t : T`, the premises
`HandlerRelated R left right h g` and `R s t` imply:

```text
Related R left right (run h p s) (run g p t).
```

The per-operation premise covers every related input-state pair and preserves
the same typed reply. The body can adapt to that reply; it has no additional
argument for inspecting hidden state. A restriction to legal states is included
in the invariant relation and preserved by the handlers, or the handlers specify
the relevant behavior outside that restriction.

## Transitive composition

Let `z : Execution U G A`, `Q : T → U → Prop`, and `right : G → List O`.
For `left : E → List O` and `middle : F → List O`, define relational composition:

```text
(R ; Q) s u := ∃ t : T, R s t ∧ Q t u
```

If `Related R left middle x y` and `Related Q middle right y z`, then:

```text
Related (R ; Q) left right x z.
```

Both premises share the actual middle execution and its observation. In
particular, its residual state witnesses the existential in `R ; Q`.

## Final-state observations

For an observation type `V`, let `stateLeft : S → V` and `stateRight : T → V`.
If:

```text
∀ s t, R s t → stateLeft s = stateRight t,
```

then `Related R left right x y` implies:

```text
(x.outcome, stateLeft x.state, observeEvents left x.events) =
(y.outcome, stateRight y.state, observeEvents right y.events).
```

Compatibility with `R` is required even when the event projections erase all
events. An arbitrary final-state publication does not follow from the relation.

## Context scope

Handler replacement compares the same reply-adaptive body under the specified
handlers and related initial states. A different claim about secret worlds,
randomized runs, joint artifact/runtime release or arbitrary linked target
contexts supplies its applicable [property experiment](../properties/experiments.md#experiment-operands)
and [disclosure contract](../properties/disclosure.md#allowed-worlds-and-selected-release).

Equal projected traces alone establish neither protocol security nor preservation
of later challenges. Erased framing or provider state can affect a later call;
the state relation and operation laws account for that effect when replacement
is claimed.

## Speculative payload and publication

[Iteration publication](iteration.md#publication) buffers tentative payload
before an actual publication action. The append law forbids using a later
abort/discard event to erase an earlier disclosure. Observers may separately
expose attempt counts or diagnostics; hiding proof payload does not hide these.
