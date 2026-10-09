# Analysis precision and framing

The independent [factor-preparation profile](../../docs/spec/profiles/compiler/factor-preparation.md)
studies checked reuse of prepared values. These choices describe that model;
they do not assert that its factor compiler is a native MLIR pass.

## Bound the cost of precision

The conservative factor rule merges facts at a call's outcomes and shares one
rewritten continuation. Asserted facts and readiness intersect; alternative phase
covers unite. Runtime replies, branches, states and guards remain distinct.
Only analysis information is weakened.

Specializing every continuation on unequal transfers is sound but can make a
chain of `n` calls produce `3*2^n-2` tree nodes, even with no query benefiting from
the precision. Sharing in memory does not help if export or checking expands
the tree. Any specialization budget must cover production, reconstruction and
the serialized result, and be checked before recursive duplication.

The [conservative rule](../../docs/spec/profiles/compiler/factor-preparation.md#conservative-typed-factor-rule)
preserves complete execution under its module laws and gives output with the
source's structural node count. This bounds neither certificate bytes nor checker
work. It forgets one-outcome facts; loop exits also forget facts unless a checked
invariant supplies them. A lost reuse falls back to direct evaluation.

The required merge law is sound weakening. Fact intersection and phase-cover
union need no complete lattice or Galois connection in every client. They use the
concrete/abstract distinction of
[abstract interpretation](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml)
at the strength this rule needs.

Compiler capacity refusal is not a protocol exhaustion event. When a budget is
exceeded, a checked direct or conservative alternative may fit; otherwise the
consumer refuses before execution. A useful measured loss of reuse can motivate
bounded specialization or richer invariants, with their own checking laws.

## State framing

A footprint lists bases, views and challenge coordinates that may change.
[Framing](../../docs/spec/profiles/compiler/factor-preparation.md#semantic-writes-and-framing)
means preservation equations for everything outside it, including aliases. An
unknown footprint preserves no prior fact, and a newly exported fact needs its
own meaning in the residual state, including after failure.

Distinct names do not prove disjointness: different handles can denote the same
storage. A native adapter must account for every affected interpreted alias.
Fixing a heap and permission algebra in the logical model would prematurely
constrain realizations whose storage remains open.

Explicit equations suffice for this finite reuse analysis. They can lose true
facts and cannot compose resource ownership. Borrowing, deallocation or concurrent
ownership may justify a richer logic, such as
[separation logic](https://www.cs.cmu.edu/~jcr/seplogic.pdf), but it must still imply
the logical frame used here. A more precise sufficient alias test can also recover
reuse without replacing that law.
