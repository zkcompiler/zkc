# One-round local-prover consumer

Let `F` be a ring with decidable equality. This profile consumes an admitted
[local prover cut](local-prover.md#local-source-admission-and-cuts)
using the [product-provider request](../providers/product-tapes.md#actual-next-request-decision).
Use that construction's provider type `D`, normalized law `q : PMF D`,
checkpoint type `View`, predicate `active : View → Bool`, and actual reached
law `ν`. Here the source result type in `View` is `Cut F`. The selected verdict
checks a single round against the polynomial `2r`.

## Committed local-prover consumer

For the [local prover cut](local-prover.md#local-source-admission-and-cuts), define:

```text
committedOnly(active,v) =
  match v.outcome with
  | returned (committed boundary) → active(v)
  | otherwise                    → false.
```

The selected source consumer uses `request(committedOnly(active),v)`. A returned
local abort then causes an outer abort without consuming a challenge. The
generic unguarded requester can consume a challenge after that same returned
local abort; equal non-accepting verdicts do not establish equal executions.

The selected probabilistic local interpreter samples each `Fin(n+1)` coin
uniformly. Its product-signature embedding preserves the returned cut and
unused provider suffix and emits no additional outer local event. The cut
itself still contains the local input vector, registers and history.

For a commutative ring with decidable equality, a committed boundary contains
claim `s` and coefficients `(a,b,c)`. The selected one-round verdict is:

```text
oneRound(s,a,b,c,r) =
  if a+a+b+c=s and a+(b*r+c*(r*r))=r+r then some () else none.
```

For `embed : D → F`, the observer applies this verdict only to an actual
returned commitment and an actual returned challenge `d`, using `r=embed(d)`.
Every other case yields `none`. This is the one-round reduction against `2r`;
it is distinct from the complete polynomial terminal in the Sumcheck profile.

For a normalized sampler with law `q`, the reduction consumer at a requesting
commitment has result law:

```text
q >>= (d ↦ pure(oneRound(s,a,b,c,embed(d)))).
```

At every other checkpoint its result law is `pure none`. An interpretation
of this consumer establishes these laws for its actual sampling operation.
The observed request experiment then has the same distribution as the
consumer, including abort, decline and exhaustion as non-acceptance.

For a field `F`, a finite `D`, injective `embed`, and `q(d)≤ε` for every `d`,
require `boundary.claim≠2` at every supported requesting commitment of `ν`.
Then the probability of `some ()` is at most `2*ε`. The accepted challenges
are roots of `a+(b-2)X+cX²`; a matching boundary and false claim make that
polynomial nonzero. Injectivity transfers its two-root bound to `D`.

The source, claim and coefficients may depend on the reached pre-draw state.
Under joint initialization, the false-claim premise is required for every
supported initial state and every supported requesting commitment of its
selected source. The conditional product law transports the supplied cap on
`q` to this actual checkpoint. Marginal uniformity with pre-draw predictability
does not establish that cap.
More general state-dependent samplers can use the corresponding reached-state
cap directly, as in the [issued-source experiment](../services/issued-causal.md#issued-causal-experiment).
