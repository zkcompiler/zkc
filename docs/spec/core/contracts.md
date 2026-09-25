# Contracts

A contract describes the complete result of an implementation at an admitted
initial state. It uses the [execution types](execution.md#complete-results),
including stopped outcomes and retained effects.

## Contract and satisfaction

For state type `S`, event type `E` and result type `A`, define:

```text
Contract S E A = {
  pre  : S → Prop,
  post : S → Execution S E A → Prop
}

Satisfies C f := ∀ s : S, C.pre s → C.post s (f s)
```

Here `f : S → Execution S E A` is the actual implementation. The postcondition
relates its initial state to its complete actual result: returned data, terminal
reason, residual state and ordered events. An unconstrained case supplies no
guarantee for that case; satisfaction supplies no guarantee outside `pre`.

An operation contract is indexed by the actual operation value and its dependent
reply type. Its arguments, configuration and instance are bound in its
interpretation. A caller establishes the precondition or uses an explicitly
defined refusal boundary. Declaring a contract does not establish satisfaction,
perform a runtime check or identify a native backend.

## Consequence

Let `C,D : Contract S E A` and `f : S → Execution S E A`. If `Satisfies C f`
and:

```text
∀ s, D.pre s → C.pre s
∀ s r, D.pre s → C.post s r → D.post s r,
```

then `Satisfies D f`. The implementation remains fixed. The new precondition
implies the established one, and the established postcondition implies the new
one on that domain.

## Sequencing contract

Let `C : Contract S E A` and `D : A → Contract S E B`. Define `C.seq D` by:

```text
(C.seq D).pre s :=
  C.pre s ∧
  ∀ first : Execution S E A, C.post s first →
    ∀ a : A, first.outcome = returned a → (D a).pre first.state

(C.seq D).post s out :=
  ∃ first : Execution S E A, C.post s first ∧
    match first.outcome with
    | stopped why =>
        out = (stopped why, first.state, first.events)
    | returned a =>
        ∃ last : Execution S E B, (D a).post first.state last ∧
          out = (last.outcome, last.state, first.events ++ last.events)
```

The precondition covers every result allowed by `C.post`. Only a returning
result requires a suffix precondition; a returned error is still such a result.
The postcondition retains the complete first result and, on a return, the
complete suffix result at the actual intermediate state.

For `f : S → Execution S E A` and `g : A → S → Execution S E B`, the premises
`Satisfies C f` and `∀ a, Satisfies (D a) (g a)` imply:

```text
Satisfies (C.seq D) (fun s => follow(f s,g)).
```

Likewise, for `h : Handler Σ S E`, `p : Proc Σ A` and `k : A → Proc Σ B`, the
premises `Satisfies C (run h p)` and `∀ a, Satisfies (D a) (run h (k a))`
imply:

```text
Satisfies (C.seq D) (run h (bind p k)).
```

This is a sufficient rule, conservative over the results allowed by the first
postcondition. It is not a weakest-precondition algorithm. A weak postcondition
may admit intermediate states that the actual implementation never produces;
composition through this rule must nevertheless cover them. A sharper proved
postcondition can remove that imprecision. Phase admission is a separate
obligation.

## Satisfaction and replacement

Two implementations satisfying one contract need not be interchangeable. For
example, `pre = True` and `post = True` permit all returning and stopping results.
That contract cannot justify replacing one implementation by another.

Replacement uses the appropriate [execution relation](observations.md#handler-replacement)
or [representation relation](../realization/representations.md#related-complete-results)
under its actual state and observation premises. A sufficiently precise contract
can help establish that relation; satisfaction alone does not supply it.

## Immutable cache validity

Let `K` be a key type, `V` a value type and `provider : K → V` one fixed pure,
total interpretation. Define:

```text
Cache K V = K → Option V

Valid provider cache :=
  ∀ key value, cache key = some value → value = provider key
```

Keys identify all immutable dependencies needed to determine the intended value.
A key can be abstract, but its actual binding to those dependencies is required.
Validity relates the actual retained values to the actual provider; equality of
names or hashes alone supplies no such relation.

The empty cache is `empty key = none` and is valid for every provider. With
decidable equality on `K`, define insertion by:

```text
insert cache key value other =
  if other = key then some value else cache other
```

If `Valid provider cache`, then inserting `provider key` at `key` preserves
validity.

## Lookup and storage policy

For a storage policy `store : Cache K V → K → Bool`, lookup is:

```text
lookup provider store cache key =
  match cache key with
  | some value => (value,cache)
  | none =>
      (provider key,
       if store cache key then insert cache key (provider key) else cache)
```

Under `Valid provider cache`, its derived laws are:

```text
(lookup provider store cache key).1 = provider key
Valid provider (lookup provider store cache key).2
```

The policy can depend on the cache. The equations describe pure values and
cache contents; they do not count native evaluations of `provider`. Other
insertion, eviction or bypass policies preserve the invariant and supply the
result and observation relation required by their clients.

A client that only receives the provider value cannot distinguish a hit by that
value. A client or observer that can inspect hit information, addresses, charges
or timing requires a relation accounting for those observations. Correct cache
contents do not by themselves establish equal complete executions or secrecy.

## Provider rebinding

Let `before,after : K → V`. If `Valid before cache` and:

```text
∀ key value, cache key = some value → before key = after key,
```

then `Valid after cache`. Agreement is required at the actual retained entries;
uncached keys can differ. An entry whose provider value changes is invalidated
or replaced before use under the new provider.

*Example.* Take `K = V = Nat`. A cache containing only the entry `1 ↦ 2` is
valid for `before k = k + 1`.
Changing the value of `after 1` to `10` invalidates that entry, even if the
provider keeps the same external name. Changing only an uncached key does not
invalidate it.

This pure-provider law does not authorize caching a stateful response, random
draw or ambient mutable read. Valid immutable data can outlive a mutation that
invalidates a [live factor fact](../profiles/compiler/factor-preparation.md#factor-state-and-facts).
Installing it into the current world still requires the applicable module and
availability law. Cache validity is separate from allocation, continuation
authority and disclosure permission.

## Preparation within a stateful context

The preparation interface extends an arbitrary external signature `Σ`:

```text
prepare(key : K) : V
external(op : Σ.Op) : Σ.Reply op
```

Its immutable provider is `provider : K → V × Nat`, containing the value and
its reference work. The key or bound provider retains every dependency of that
pair. Lookup and insertion prices are explicit. The reference handler state is
`Cache K (V × Nat) × S`; an external handler has state `S`.

- Preparation returns the provider value, preserves `S`, updates only the
  cache according to the direct or memoizing policy, and records work, saved
  work and overhead.
- An external call preserves the cache and retains the external handler's
  actual reply or stop, resulting state and ordered events. It can consume
  randomness or fail after changing state.

Relate direct and memoized states when both caches are valid for the same
provider and their external states are equal. For every finite reply-adaptive
body over this interface, execution preserves the outcome, that state relation
and the ordered external events. The selected event observation removes the
accounting records. Resolving each preparation call directly to its immutable
value also relates the unprepared reference to either policy, with cache
validity and the same external state.

These are contextual execution laws under this interface: the caller receives
prepared values and actual external replies, but cannot inspect the cache or
accounting to choose its next operation. Because every policy satisfies them,
which one a compiler installs is
[a cost question, and a repeated preparation is first removed as an ordinary repetition](../../rationale/preparation-reuse.md). An observer of costs, addresses or
timing requires its own relation. Equal protocol observations do not establish
profitability. The pure provider is total and cannot inspect mutable state;
allocation failure inside preparation, concurrent cache access, reentrancy or
cache-dependent scheduling require additional contracts.

Event emission is an external signature with unit replies, a unit state and
one event per call. Its specialized embedding retains the adaptive preparation
reference interpreter's exact cache, result, events and cost equations. It does
not require a second preparation interface.
