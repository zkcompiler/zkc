# Operation interpretations

An operation interpretation implements each operation of one signature by a
[body](execution.md#bodies) over another signature. It preserves that operation's
logical reply type. This permits staged implementation while leaving source
meaning independent of a particular compiler representation.

## Interpretation interface

For signatures `Σ` and `Τ`, define:

```text
OperationInterpretation Σ Τ = (op : Σ.Op) → Proc Τ (Σ.Reply op)
```

An interpretation `θ` can implement an operation with zero, one or several
target calls. Its body can branch on their replies and can stop. Its returned
reply, if any, has exactly the type expected by the source continuation.
State, events and stopping behavior acquire meaning through the selected
target handler.

This interface does not itself relate different native representations of a
reply. Such a claim uses the [representation relation](../realization/representations.md#related-complete-results).

## Body interpretation

For `θ : OperationInterpretation Σ Τ`, define
`interpret θ : Proc Σ A → Proc Τ A` by:

```text
interpret θ (done a)   = done a
interpret θ (halt r)   = halt r
interpret θ (call o k) = bind (θ o) (fun a => interpret θ (k a))
```

The source continuation receives the expansion's actual returned reply. A
stopped expansion skips that continuation under the common
[sequencing rule](execution.md#sequencing).

For `p : Proc Σ A` and `k : A → Proc Σ B`, interpretation preserves
[body composition](execution.md#body-composition):

```text
interpret θ (bind p k) = bind (interpret θ p) (fun a => interpret θ (k a))
```

## Identity and composition

The identity interpretation of `Σ` is:

```text
identityΣ op = call op done
```

For a third signature `Υ`, `θ : OperationInterpretation Σ Τ` and
`φ : OperationInterpretation Τ Υ`, their composition implements `Σ` in `Υ`:

```text
(φ ∘ θ) op = interpret φ (θ op)
```

The following laws are equalities of mathematical bodies:

```text
interpret identityΣ p = p
interpret φ (interpret θ p) = interpret (φ ∘ θ) p
```

The intermediate signature need not be a compiler IR. These equations impose
no serialization of continuations or expansion into a physical tree.

## Execution fusion

Let `θ : OperationInterpretation Σ Τ` and `h : Handler Τ S E`. Their composite
source handler is:

```text
composeHandler θ h op s = run h (θ op) s
```

For every `p : Proc Σ A` and `s : S`, the fusion law is:

```text
run h (interpret θ p) s = run (composeHandler θ h) p s
```

This is equality of complete results, including residual state and the ordered
events of every reached target call. It includes target calls that stop partway
through an expansion.

Fusion compares the interpreted target body with the source using its composite
handler. A target context allowed to insert new actions between expanded calls
has a different interface; preservation under such contexts requires a separate
argument.

*Example.* An expansion first emits `1` and increments a natural-number state,
then emits `2`, increments the state again and stops with `abort`. Starting
from state `7`, the expanded operation yields `(stopped abort, 9, [1,2])`.
Fusion retains both increments and events. Replacing the expansion by its second
call alone would instead leave state `8` and events `[2]`.

For a [lawful outer monad](execution.md#outer-effects) `M` and
`h : MonadHandler M Τ S E`, the corresponding law is:

```text
runM h (interpret θ p) s =
  runM (fun op t => runM h (θ op) t) p s
```

The equality has type `M (Execution S E A)`. It does not add normalization,
independence or an outer-exception recovery contract.

## Sequencing and changing construction order

Independently interpreted components sequence through the prefix's **actual
residual state**:

```text
run h (interpret θ (bind p k)) s =
  follow (run h (interpret θ p) s)
    (fun a t => run h (interpret θ (k a)) t).
```

This follows from interpretation preserving binding and execution fusion.
It retains prefix events, a stopped prefix and failure within the suffix.
Resetting or rebasing state at the connection is a different claim. For an
actual prefix result `e`, suffix execution `next` and state map `rebase`, the
sufficient premise is:

```text
∀ a, e.outcome = returned a → next a e.state = next a (rebase e.state).
```

Only then may `follow e next` replace the suffix's input state by its rebased
state. This equality includes the suffix's final state and events. A weaker
observer or heterogeneous state change needs its corresponding result relation.
The premise is vacuous after a stopped prefix because its suffix never runs.

Similarly, two-stage construction agrees with a selected direct construction
`δ` when every actual source operation satisfies the square:

```text
∀ op, interpret φ (θ op) = δ op
  ⇒ interpret φ (interpret θ p) = interpret δ p.
```

Interpretation associativity alone does not establish this square or authorize
exchanging two constructions. Fresh and transcript-derived challenges can use
different providers and laws. Even within one framed construction, resetting
the transcript between components can change the next challenge.

## Preservation of operation laws

Fix `models : Handler Σ S E → Prop` and `before, after : Proc Σ A`. Suppose
the source equation is justified by:

```text
∀ g : Handler Σ S E, models g →
  ∀ s : S, run g before s = run g after s.
```

If the actual composite handler satisfies `models (composeHandler θ h)`, then:

```text
∀ s : S, run h (interpret θ before) s = run h (interpret θ after) s.
```

The model predicate can include algebraic, state and observation requirements.
An operation name or compatible reply type alone establishes none of them.
This law transports an established source equation under its actual premises;
it is not a cryptographic construction reduction.

## Phase admission

Let `P` and `Q` be [interactions](../language/interaction.md#roles-and-phases)
over `Σ` and `Τ`. An admission for `θ` consists of a phase relation
`R : P.Phase → Q.Phase → Prop` and the following operation law:

```text
∀ phase op lowerPhase,
  P.enabled phase op → R phase lowerPhase →
    Conforms Q (θ op) lowerPhase ∧
    Returns Q (fun a last => R (P.advance phase op a) last) (θ op) lowerPhase
```

[Conforms and Returns](../language/interaction.md#all-reply-conformance)
quantify over all typed replies. The operation law covers the whole expansion
at every related entry. Every returning target path relates its actual final
phase to the source phase advanced by that same returned reply. Stopped paths
have no return-phase obligation; their complete execution remains governed by
fusion.

For `p : Proc Σ A` and `post : A → P.Phase → Prop`, the premises:

```text
Conforms P p phase
Returns P post p phase
R phase lowerPhase
```

imply both:

```text
Conforms Q (interpret θ p) lowerPhase

Returns Q
  (fun a last => ∃ upperPhase, post a upperPhase ∧ R upperPhase last)
  (interpret θ p) lowerPhase
```

A legal entry without the returning relation cannot justify the source suffix.
Role locality, endpoint inputs and native or probabilistic correspondence remain
additional contracts.

## Expansion bounds

For natural numbers `n` and `m`, suppose:

```text
Within n p
∀ op : Σ.Op, Within m (θ op)
```

Then the [uniform call bound](execution.md#uniform-call-bounds) transports as:

```text
Within (n * m) (interpret θ p).
```

The operation premise is uniform over actual operation values, including their
arguments and every typed target reply. A bound for one operation spelling or
one successful run is insufficient. This particular sufficient rule uses a
constant expansion bound; a more precise source-dependent bound needs its own
proof. Call counts do not automatically measure field arithmetic, native work
or cryptographic queries.

## Iterated interpretations

Interpretation commutes with each finite [controller prefix](iteration.md).
Per-step conformance and return invariants transport admission through prefixes;
per-step complete simulation transports actual residual state and observations.
A proof for all prefixes does not supply provider progress, an infinite-trace
measure or eventual successful production.
