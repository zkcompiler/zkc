# Analysis precision has a bounded representation cost

After a call whose success and failure transfer different facts, the compiler's
default is the
[conservative factor rule](../spec/profiles/compiler/factor-preparation.md#conservative-typed-factor-rule):
both outcomes weaken to one sound description and share one rewritten
continuation. The returned Boolean and the source's own branches stay. Merging
analysis information merges no runtime state and moves no guard. The
[merge law](../spec/verification/analysis.md#merging-descriptions) gives the
condition: asserted facts and readiness intersect, alternative phase covers
unite. Specializing a continuation on an outcome is an explicit option under a
global growth and work budget, stated in the
[analysis design](../compiler/design.md#3-analysis-and-optimization-interfaces).
The budget is checked before any recursive duplication and covers production,
the checker's reconstruction and the serialized result.

## Alternatives

**Specialize the continuation whenever the two transfers differ.** The
[typed factor rule](../spec/profiles/compiler/factor-preparation.md#typed-factor-rule)
does this and is sound. It duplicates the suffix. A chain of `n` calls with
unequal availability transfer yields a syntax tree of size `3*2^n-2`, even when
the suffix contains no query that could use the extra facts. The linear bound
proved for equal transfers does not cover this case.

**Share continuations in memory and expand them at the boundary.** A graph that
becomes an exponential tree for export or for checking has not bounded the size
where the consumer pays for it.

**Require a complete lattice and a Galois connection of every analysis.**
Abstract interpretation separates concrete meaning from an approximating
analysis [1]. The obligation needed here is weakening at a merge. A list of
asserted facts meets it by intersection and a cover of phases by union, without
the full framework.

**When the budget runs out, start the protocol and stop it as `exhausted`.** A
compiler or checker limit is not a protocol event. The compiler falls back to a
checked direct alternative or a proved conservative merge. If neither fits the
consumer's capacity it reports a capacity refusal before execution, in line
with the [failure boundaries](../spec/verification/judgments.md#failure-boundaries).

## Reason

The conservative rule preserves complete execution under the same module laws,
including source stops and readiness refusal, and its output plan has exactly
the structural node count of its source. Its cost is explicit: assertions that
hold on only one outcome are forgotten, and a query falls back to direct
evaluation when no retained fact is eligible. Loop bodies stay structured and
direct, and the facts at a loop exit are forgotten unless a checked invariant
supplies them. The node count bounds neither certificate bytes nor checking
work, which need their own evidence. A different rewrite needs its own rule and
proof; the theorem of one rule is not reused for another.

## Reopen when

A measured client loses a reuse that matters because a merge forgot a fact that
holds on one outcome, and budgeted specialization, loop-invariant inference or
a shared typed region recovers it while the exported and checked size stays
bounded.

## References

1. Patrick Cousot and Radhia Cousot, "Abstract interpretation: a unified
   lattice model for static analysis of programs by construction or
   approximation of fixpoints," *POPL 1977*, pp. 238–252.
   [Author page](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
