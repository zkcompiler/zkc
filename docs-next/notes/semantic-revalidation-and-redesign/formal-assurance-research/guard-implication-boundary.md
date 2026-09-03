# The guard-implication boundary and its sound extension

> **Kind:** research note (formal-assurance research, Core admission)
> **State:** Written 2026-09-03 from the Terminal-contract migration and the
> holdout re-adjudication; no owner change proposed; a trigger is named.
> **Authority:** None.

## 1. The boundary as the page states it

Core admission decides guard implication by one closed syntactic law
(`docs-next/pir/interactive-core.md`, Section 10): a use guard implies a
source guard exactly when the source guard is `Always` or the two guards are
structurally identical bodies. The page says that a mathematically valid but
syntactically different implication is outside this regime and that a checked
implication satellite would need its own proposition, validator, bounds, and
admission integration. The migrated Terminal contract inherits the same
boundary: a terminal can require a Reduction only when `AttemptedWhenever`
holds, and with unguarded scope openings that means the Reduction is
unconditional or shares the terminal's exact guard body. The Check obligation
is finer, because it reads the terminal Guard's term through the must-fact
analysis, but that analysis relates a term to its own inputs, not two terms
to each other.

## 2. What the boundary costs

Fold-then-check protocols author a Reduction under a partial condition and
accept under the full condition: the fold applies when the sumcheck rounds
pass, the final consistency checks are computed on the folded object, and
acceptance requires everything. Under the boundary the natural authoring,
fold guarded by the partial conjunction and Accept guarded by the full one,
is refused twice over: the terminal cannot require the fold, and the claim
liveness law cannot see that the folded claim is live at Accept, because the
two guards are different bodies.

The holdout re-adjudication shows the cost is bounded for the protocols in
the portfolio: WHIR is authored with unconditional Reductions, a single
Accept guarded by the conjunction of all five Checks, and a fallback Reject.
An unconditional fold is the standard verifier's shape, since the verifier
computes everything and accepts only when every check holds. The boundary
bites only when a Reduction must be conditional: when its side inputs exist
only on a branch, for example an Oracle answer queried only after a Check
passed, or when the protocol's semantics require an early stop before a
Reduction that would otherwise apply.

## 3. The sound extension

A checked implication between two guard terms over shared inputs can be
decided by the same must-fact analysis with one extra bit. Call a Boolean
term exact when it returns true if and only if every literal in its
`when_true` set holds; an input variable is exact, a conjunction built as
`if c then a else false` from exact operands is exact, and a term whose
`when_true` set is `Impossible` is exact. The analysis computes exactness
structurally alongside the must-facts. Then

```text
GuardImpliesStructurally(later, earlier) :=
  Exact(GuardTerm(earlier))
  and MustWhenTrue(GuardTerm(earlier)) subset MustWhenTrue(GuardTerm(later)),
  literals compared by the exact ValueRef each input ordinal names
```

is sound: on every path on which the later guard is true its must-literals
hold, those include every must-literal of the earlier guard, and exactness
makes the earlier guard true. It is decided in time linear in the two terms.
It admits the fold-then-check authoring above, because the partial
conjunction is exact and its literals are among the full conjunction's. It
still refuses an implication that depends on a primitive's meaning or on a
disjunction, which stays outside the regime as today.

## 4. What adopting it would change

The law would join `GuardImplies` in Section 10 as a second closed
implication, used by the liveness simulation, by `AttemptedWhenever`, and by
the required-Reduction clause of the Terminal contract. The Core body grammar
does not change, so no identity rotates from the grammar; the admission law
changes, so the Interaction profile and its dependents rotate. The terminal
path-algebra and owner-projection packages would extend their region
implication from atom-set inclusion to the new law, and the mechanization
would add exactness to its must-fact transcription and prove the soundness
argument above rather than the finite oracle.

## 5. Trigger and non-claims

Adopt the extension when a selected protocol needs a conditional required
Reduction that the unconditional authoring cannot express; until then the
boundary holds and costs nothing the portfolio has shown. This note proves
nothing mechanically: the soundness argument is a sketch to be transcribed
when the trigger fires, and no owner page changes now.
