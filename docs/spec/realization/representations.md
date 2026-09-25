# Representations and complete execution

A representation relates a logical result to a result carried by another
execution. It can relate different value types, heaps and event alphabets.
A returned reference denotes its value in the actual state left by execution.

This applies to [family ingress](../profiles/source/families.md) and
[iteration](../core/iteration.md) as well as individual operations. Related
ingress results select related dependent inputs in their actual residual states;
the corresponding member law then yields a relation of the complete family
runs. For iteration, the relation also covers pending continuation values and
preserves continue/finish tags. Neither application grants input validity,
phase compatibility or progress without its separate premises.

## Outcome and state relations

Let `S, T` be state types, `A, B` result types, `E, F` event types, and `O`
an observation type. Select:

```text
R     : S → T → Prop
V     : A → S → B → T → Prop
left  : E → List O
right : F → List O
```

`R` relates residual states. `V a s b t` states that result `b` in state `t`
represents result `a` in state `s`. The functions `left` and `right` are
ordered [event projections](../core/observations.md#event-projections) into `O`.

For any value relation `W : A → B → Prop`, lift it to outcomes by:

```text
OutcomeRel W (returned a) (returned b) = W a b
OutcomeRel W (stopped r) (stopped q)   = (r = q)
OutcomeRel W (returned a) (stopped q)  = False
OutcomeRel W (stopped r) (returned b)  = False
```

This lifting preserves the common logical stop reason exactly. An adapter from
a different native exit vocabulary supplies its interpretation into the selected
result model; the relation does not infer that interpretation from an exit code.

## Related complete results

For `x : Execution S E A` and `y : Execution T F B`, define:

```text
Relates R V left right x y ⇔
  R x.state y.state ∧
  OutcomeRel (fun a b => V a x.state b y.state) x.outcome y.outcome ∧
  observeEvents left x.events = observeEvents right y.events.
```

The two states in `V` are the actual final states of these executions. The
relation retains final states and ordered projected events on stopped outcomes
as well as on returns. A stopped pair has no returned-value obligation.

A scalar representation may use a state-independent `V`. A handle representation
MUST establish the intended domain object in its owning post-state. Literal
equality of private native heaps is unnecessary when `R` and `V` establish the
selected logical correspondence.

*Example.* A logical return of `7` can correspond to slot `0` in the final heap
`[7]` under `V a s slot heap ⇔ heap[slot]? = some a`. Slot `0` in heap `[8]`
does not represent that return. The numeric slot alone cannot distinguish them.

The common [equal-result relation](../core/observations.md#execution-relation)
is included by choosing `V a s b t ⇔ a = b`. This specialization still retains
the chosen state relation and event projections.

## Sequencing represented values

Suppose `Relates R V left right x y`. For suffixes
`f : A → S → Execution S E C` and `g : B → T → Execution T F D`, let
`W : C → S → D → T → Prop` be their result relation. If:

```text
∀ a s b t, R s t → V a s b t →
  Relates R W left right (f a s) (g b t),
```

then:

```text
Relates R W left right (follow x f) (follow y g).
```

The premise relates consumers of the represented results at their residual
states. It includes returned data that represents a recoverable error. A
stopped prefix invokes neither suffix and retains its state and event prefix.

This sufficient rule quantifies over every pair described by `R` and `V`.
A claim restricted to a smaller reachable domain supplies a strengthened
invariant or a separate proof for those actual pairs; it cannot omit a suffix
premise needed by an actual returning prefix.

## Transitive composition

Let `z : Execution U G C`, with second relations
`R₂ : T → U → Prop`, `V₂ : B → T → C → U → Prop`, and event projection
`right₂ : G → List O`. Write `middle : F → List O` for the first comparison's
right projection. If:

```text
Relates R  V  left  middle x y
Relates R₂ V₂ middle right₂ y z,
```

the composite relations are:

```text
R₁₂ s u ⇔ ∃ t, R s t ∧ R₂ t u

V₁₂ a s c u ⇔ ∃ t b,
  R s t ∧ R₂ t u ∧ V a s b t ∧ V₂ b t c u.
```

They establish `Relates R₁₂ V₁₂ left right₂ x z`. The proof uses the same
actual execution `y`, its state and, on return, its value. Both premises use
the same `middle` projection. Independently chosen middle subjects or
incompatible interpretations need an explicit bridge before applying this law.

The state conjuncts in `V₁₂` keep its middle value witness in a state related
to both endpoints. A value witness from an unrelated heap does not suffice.

## Observers

A coarser observation is valid when it is determined by the established
relation. For example, applying the same function to equal projected event
lists preserves their equality. A final-state or result observer additionally
requires a law that `Relates`-related complete results receive equal observations.

Event equality alone supplies no law for arbitrary memory, timing or allocation
observers. Nor does representation correspondence establish replacement in an
arbitrary target context that can inspect hidden representation details. The
allowed suffixes and observers are those justified by the selected relation.

## Acceptance and output realization

A relation target can realize a selected verifier's acceptance and exposed
outputs without reproducing its complete execution. Fix:

```text
Input       : Type
Output      : Input → Type
Witness     : (i : Input) → Output(i) → Type
accepts     : (i : Input) → Output(i) → Prop
constraints : (i : Input) → (o : Output(i)) → Witness(i,o) → Prop.
```

`Acceptance(accepts,constraints)` requires both directions:

```text
sound    : ∀ i o w, constraints(i,o,w) → accepts(i,o)
complete : ∀ i o, accepts(i,o) → ∃ w, constraints(i,o,w).
```

Consequently, `∃ w, constraints(i,o,w) ↔ accepts(i,o)` for each actual input
and output. The soundness direction quantifies over **every satisfying witness**,
including assignments not produced by a supplied honest witness generator.
Output and internal witness representations can be indexed by the input.

The predicate `accepts` MUST describe the selected subject independently of the
target constraints. For a deterministic `verify : (i : Input) → Terminal(Output(i))`,
use its graph `verify(i) = accepted(o)`. For an effectful verifier, connect the
actual execution's `returned(accepted(o))` outcome or an explicitly selected
result observation. Merely repeating the condition that some output is accepted
at every `o` does not bind the returned output. A genuinely relational source
can have multiple outputs; deterministic behavior is not required universally.

For a consumer predicate `use(i,o)`, the contract gives:

```text
(∃ o w, constraints(i,o,w) ∧ use(i,o)) ↔
  ∃ o, accepts(i,o) ∧ use(i,o).
```

Both conjuncts use the same actual output. Decision-only verification specializes
`Output` to `Unit`. A returned residual obligation can instead be passed to its
next consumer; prefix acceptance does not discharge that obligation. The
[component connection laws](../properties/relations.md#component-connections)
apply to different output types with an explicit connector.

A source-to-target input map `bind : SourceInput → Input` additionally requires
`sourceAccepts(s,o) ↔ accepts(bind(s),o)` for its selected source predicate.
Source, proof, parameters, original objects, ordered points and provider state
remain bound wherever the predicate depends on them. Decoding, admissible input
coverage and actual output representation laws are not inferred by naming the
same types.

Each instance MUST identify its quantifier partition: fixed statement and
verifier environment in `Input`, exposed results in `Output`, and existential
assignments in `Witness`. A supplied proof may be part of the fixed input;
existentially closing that proof for an outer relation is a separate, explicit
choice. Interactive coins supplied by an experiment remain bound to that run.
Acceptance for some freely chosen challenge does not establish the experiment's
soundness. If a derived challenge is represented by an internal witness, the
constraints tie it to the selected construction's actual transcript, parameters
and derivation. Its value cannot be an unconstrained existential substitute.
These requirements concern the chosen types and predicates; they impose no
universal metadata record. Cryptographic assumptions about the derivation remain
separate from acceptance adequacy.

[`Zkc.Realization.Acceptance`](../../../formal/Zkc/Realization/Acceptance.lean)
implements these laws. They do not imply the complete-result relation above,
cryptographic soundness, honest protocol completeness or outer-proof security.
The one-direction [reduction contract](../properties/relations.md#soundness-direction-reduction)
remains appropriate for reductions with residual obligations and bad events;
it is not strengthened to exact acceptance realization.

## Source-selected adapters

A concrete adapter MUST connect the consumer's selected source and operation
site to its actual arguments and transitions. This connection includes ordered
inputs, captures, domain, operation contracts and result interface.

Before erasing a meaningful distinction, the adapter retains its interpretation,
establishes it at the proper checked boundary, or supplies an applicable erasure
law. Type equality alone does not justify a changed field, operand order, guard,
coordinate sequence, lifetime or implementation.

Replacing an implementation requires the selected relational contract. Two
implementations satisfying a weak unary contract need not be interchangeable;
the distinction follows the common [contract boundary](../core/contracts.md#satisfaction-and-replacement).

## Algebra and provider correspondence

A primitive adapter binds the actual mathematical domain and the laws used by
its consumers, together with representation, ranges, shapes and failure behavior.
Codec, algebra and provider correspondence are separate obligations even when
one library implements them all.

A provider correspondence includes actual framing, source occurrences,
persistent transitions and the selected joint initialization law. Reducing a
digest to a field element denotes the pushforward of the actual digest law;
uniformity requires an additional probability argument.

Reuse of a deterministic encoding or provider computation preserves the
selected absorption order, draw order and observer. Equality of an arithmetic
return alone does not justify removing or moving provider transitions. The
[probability specification](../properties/probability.md) supplies the relevant law operands;
a deterministic same-provider equation does not create a fresh-coin theorem.

## Storage and ownership

A native reference MUST resolve within its declared world or session and
lifetime to the intended domain, shape and contents. Allocation and mutation
preserve or invalidate relevant references and facts according to their
contracts, including aliases and reuse of a physical location.

Generations, generative identities or another adequate ownership construction
may implement this rule. Freshness in an allocator's pool is relative to that
pool. Preserving caller-visible names additionally requires their registration
or reconciliation with the actual world; pool freshness alone is not global
native-name freshness.

Immutable cache validity, facts about live state, allocation ownership and
continuation authority have different premises. One content digest or reference
tag does not establish all four. The [factor-state profile](../profiles/compiler/factor-preparation.md)
specifies one concrete collection of these state and allocation laws.

## Capacity and progress

A native realization MUST state its admitted resource and progress domain.
Finite mathematical call bounds do not prove machine integer bounds,
allocation success, kernel termination or bounded event storage.

A public capacity check may reject a target configuration before execution
while leaving logical inputs and providers unchanged. That rejection is an
admission or start result, not an extra logical protocol stop. Source-defined
exhaustion and allocation failure still occur at their specified execution
points. Introducing or deleting a logical stop requires a corresponding
[transformation law](../verification/refinement.md#effects-and-admission-timing).

The complete-result relation compares completed executions. A native progress
claim additionally establishes completion on its admitted domain or states its
explicit progress assumption. It is not obtained from mathematical well-founded
syntax alone.

## Completion and atomicity

A completed native result MUST retain the modeled residual state and ordered
observations on success and failure. A failed call has no implicit rollback.
Host interruption without this correspondence is distinguished from a completed
logical result.

Synchronous completion establishes the promised end of buffer accesses and
recovery of ownership. Callbacks, resumption, interleaving or device overlap
require an execution contract supporting those behaviors. A native scheduler
cannot silently replace an [atomic call](../core/execution.md#call-boundary)
by observably interleaved steps.

## Admission and custody

Native execution MUST use the subject and decoded plan bound by successful
admission, under the consumer's selected interpretation and policy. The admitted
object prevents unchecked plan substitution between checking and execution.
Invocation binds actual inputs and providers and establishes initial premises.

Compilation specialization and runtime immutable captures have different
lifetimes. A runtime capture is not automatically public compiler input.
[Binding and artifacts](artifacts.md) define the corresponding evidence,
identity and custody obligations.

## Raw objects and lawful arithmetic images

An adapter can retain original bytes, a decoded raw object and a lawful
arithmetic image as three different subjects. Decoding, conversion and arithmetic
commutation require separate laws. Observation preservation concerns the subject
actually absorbed or published by the construction; conversion to a subgroup
image need not preserve the original object or its bytes. A scalar-multiplication
API does not establish a field-module instance for torsion-bearing raw points.
Valid group or integer-action laws can still apply to such a raw domain.

Choose correspondence for the claimed consumer: acceptance and exposed outputs,
successful proof bytes under coupled choices, complete service simulation, or
security-experiment transport. None implies the others without additional laws.
In particular, existence of accepting verifier coins is not a soundness bound.
