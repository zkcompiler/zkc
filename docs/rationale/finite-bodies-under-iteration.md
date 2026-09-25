# Finite bodies remain inspectable under iteration

[Outer iteration](../spec/core/iteration.md) composes finite effectful bodies,
retaining the existing endpoint kernel. Explicit pending prefixes describe an
unbounded reference without assigning that reference a finite endpoint bound.

## Alternatives

A capped endpoint alone cannot describe success beyond its cap or divergence.
Treating proof fuel as exhaustion changes operational meaning. An opaque provider
implementing the whole loop hides protocol work from analysis. Conversely,
replacing every finite program with a coinductive calculus adds termination and
bisimulation obligations to all current finite passes without a demonstrated
need inside their stored bodies.

## Reason

Finite-prefix composition reuses existing sequencing, phase admission and
interpretation laws. It retains actual state and events through failed attempts.
Publication and deployment budgets stay explicit contracts. Retrying is one use;
the construction also handles iterative search and segmented services.

Capretta's partial computations and Interaction Trees provide broader recursive
models. They motivate separating pending computation from failure; their results
are not imported proofs of this model.

## Reopen when

An admitted use requires recursive stored bodies, infinite externally interactive
traces, fairness, or interruption within a step, and finite segmentation cannot
preserve its chosen observations. Such evidence warrants a richer calculus and
its own compatibility theorem rather than an opaque recursive primitive.

## References

- Venanzio Capretta. *General Recursion via Coinductive Types*. Logical Methods
  in Computer Science 1(2:1), 2005, pp. 1–28.
  [Paper](https://lmcs.episciences.org/2265).
- Li-yao Xia et al. *Interaction Trees: Representing Recursive and Impure
  Programs in Coq*. PACMPL 4 (POPL), Article 51, 2020.
  [Paper](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf).
