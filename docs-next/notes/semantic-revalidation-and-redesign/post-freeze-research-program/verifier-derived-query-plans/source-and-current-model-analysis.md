# Source and Current-Model Analysis

## Source pressure

Four materially different families expose the same architectural question:

- DEEP-ALI defines verifier-side quotient functions by reading prior words and
  combining those answers with public out-of-domain claims.
- STIR defines virtual quotient and folded words whose finite branch selects a
  prior source word or a public fill value, followed by nested folding.
- Circle FRI batches answers from several source words by a verifier-known
  linear combination.
- WHIR groups a fixed finite fibre of source reads before a fold computation.

The papers motivate the shape. They do not, by citation alone, establish that
the bounded witness is an exact encoding of any complete source protocol.

## Existing target capabilities

The active `InteractiveCore` already provides the executable atoms required by
all four shapes:

1. exact-domain immutable Oracles with ordinary query and answer occurrences;
2. typed total portable derived values;
3. public-data-dependent guards and explicit terminal paths;
4. finite static occurrence order, scope, and causal admission; and
5. replay and transcript meaning attached to actual Core observations.

The missing object was not another executable Oracle kind. It was an
identified, checkable explanation of how one logical read expands to a finite
set of guarded source reads and pure computations.

## Required invariants

Any shared boundary had to preserve all of the following:

- no invented prover publication or strategy authority;
- no new transcript observation merely because a logical word is named;
- no ambient callback or runtime occurrence allocation;
- exact route exhaustiveness and explicit partial-operation terminals;
- no source-answer-dependent allocation, suppression, or retargeting of later
  reads in the selected profile;
- exact logical order and multiplicity, even when physical indices coincide;
- independent admission of the executable flat Core; and
- separate ownership of source correspondence and theorem claims.

These constraints are shared by the source shapes but are independent of each
paper's security theorem.
