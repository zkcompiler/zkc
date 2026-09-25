# A frame is a set of preservation equations, not a separation logic

The [factor-state profile](../spec/profiles/compiler/factor-preparation.md#semantic-writes-and-framing)
states framing directly. A footprint lists the bases, views and challenge
coordinates an operation may write. The frame relation says that every other
base, view and coordinate denotes the same thing afterwards, aliases included.
A fact survives a call when a sufficient test places its referents outside the
footprint. An unknown footprint preserves no old fact, and a fact exported by
the call needs its own meaning in the state the call leaves.

## Alternatives

**Adopt separation logic.** Reynolds shows why ordinary conjunction cannot
extend a local mutation specification once names may alias, and gives a frame
rule built on separating conjunction with a side condition on the modified
variables [1, §4]. Using it means choosing a heap model and a permission
algebra. The worlds this law describes are logical: total functions from keys,
handles and coordinates to values. Buffers and lifetimes, which a heap model
would describe, belong to a native realization that is free to choose them. A
heap model fixed ahead of that choice would constrain it with no consumer.

**Infer separation from distinct names.** Borrowing the vocabulary of
disjointness proves nothing: two handles with different names can refer to the
same storage. The profile therefore requires a native adapter to include every
interpreted alias its writes affect, and gives a different name no meaning.

## Reason

The explicit law is sound for the finite analysis that uses it, and what it
gives up is known. It can discard a fact that is still true, and it cannot
compose ownership of resources. Either loss only makes an optional reuse
unavailable, in which case the direct evaluation is selected. A more precise
alias analysis or ownership discipline may replace the sufficient test as long
as it implies the same frame relation.

## Reopen when

Borrowing, deallocation, overlapping slices or concurrent ownership in a
supported realization needs resource composition that can be reused across
operations. The richer logic must still imply the logical frame that the
consumers of facts rely on.

## References

1. John C. Reynolds, "Separation Logic: A Logic for Shared Mutable Data
   Structures," *LICS* 2002, pp. 55–74, §4 (frame rule).
   [Author PDF](https://www.cs.cmu.edu/~jcr/seplogic.pdf).
