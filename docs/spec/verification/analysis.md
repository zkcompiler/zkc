# Sound analysis and phase checking

An analysis computes descriptions used to justify a transformation or admission
claim. Its meaning and soundness concern the actual operations and states of
that claim. A conservative analysis may lose information or decline a program
that satisfies the underlying semantic judgment.

## Meaning and transfer

For abstract descriptions `X` and concrete states `S`, write
`Means : X → S → Prop` for the analysis's selected meaning. A transfer law
connects an input description to the actual transition and the description of
its resulting state. If the transfer depends on an operation result, it uses
that actual result and residual state, including the specified failure branch.

A sound weakening from `x` to `y` satisfies
`∀ s, Means x s → Means y s`. Thus it may forget facts without declaring an
unjustified new fact. Which facts survive a mutation depends on the actual
effect and alias contract. An unknown effect supplies no purity premise.

These are requirements on the chosen analysis meaning and transfers. They do
not prescribe a universal abstract domain, lattice, least fixed point or
Galois connection. The [finite phase profile](../profiles/compiler/finite-phases.md) gives an exact selected
instance. The [factor profile](../profiles/compiler/factor-preparation.md) supplies a different interpretation
of facts, availability and result-dependent module summaries.

## Summaries and exact consumers

For a selected observation `observe : S → O`, a summary `summarize : S → A`
and meaning `means : A → O → Prop` are sound when:

```text
SummarySound observe summarize means ⇔
  ∀ s, means (summarize s) (observe s).
```

A summary computed after erasure uses the actual composite function
`summarize = analyze ∘ encode`. The summary justifies a property only when
every observation described by its meaning satisfies that property. Sound
weakening can forget facts. Two sound descriptions of the same actual
observation can be combined by conjunction; this is not the merge of
alternative control-flow entries defined below.

For example, an unknown Boolean description that admits both values is sound
after complete erasure of a Boolean. It cannot recover that Boolean or justify
assuming it is false. Exact recovery instead needs the
[consumer factorization law](refinement.md#remaining-consumers). An analysis
may decline an optional rewrite when precision is insufficient; it cannot
discard a required protocol check or assert an unsupported fact.

## Merging descriptions

A merged description `z` for alternative entries `x` and `y` is sound when:

```text
∀ s, (Means x s ∨ Means y s) → Means z s.
```

This is weakening from each alternative to the same description. The concrete
state is unchanged by this analysis step. The meaning of a description determines
how it can be merged: a list of facts asserted together can retain facts justified
on both alternatives, while a cover of possible phases contains both alternatives.
The [finite phase merge](../profiles/compiler/finite-phases.md#abstract-phase-policy)
therefore uses union. A generic list operation alone does not define a sound merge.

## Factor analysis and proposals

The selected factor analysis proposes direct evaluation or reuse of an eligible
fact. Its value theorem requires validity of the actual fact context. Its
readiness theorem separately requires the query's availability premise. A
checked value identity alone cannot manufacture an unavailable input.

The [typed factor rule](../profiles/compiler/factor-preparation.md#typed-factor-rule)
specifies its concrete transfers, loop treatment and invariant premises.
Proposal generation may be heuristic; accepted use requires the selected
[checked transformation](refinement.md#checking-the-actual-candidate) or another
sound judgment. Search failure does not prove semantic impossibility.
