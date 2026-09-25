# Probability and persistent state

A probabilistic execution assigns mass to complete results. Its state carries
the resources that later calls use; its observation specifies which information
is available to the participant or recipient of a claim. The
[experiment](experiments.md#experiment-operands) fixes both interpretations.

## Normalized discrete distributions

For a type `X`, a probability mass function consists of nonnegative point masses
whose sum is one:

```text
PMF X = { p : X → [0,∞] | Σx p(x) = 1 }
support(p) = { x | p(x) ≠ 0 }.
```

The sum is the unordered sum of nonnegative terms. Normalization makes every
point mass finite and the nonzero support at most countable. The notation
`[P]` is one when the mathematical proposition `P` holds and zero otherwise.
It does not assert that an implementation can decide `P`.

For `p : PMF X`, `f : X → Y`, and `k : X → PMF Y`, define:

```text
pure(x)(x')      = [x' = x]
map(f,p)(y)      = Σx [f(x) = y] p(x)
bind(p,k)(y)     = Σx p(x) k(x)(y)
Pr[p : B]       = Σx [B(x)] p(x).
```

Here `B` is an event on `X`. These operations retain total mass one; in
particular, `bind` does so because every selected `k(x)` is normalized.
Probabilities lie in `[0,1]`. A deterministic execution embeds by `pure`.

For a signature `Σ`, state `S`, event `E` and result `A`, a probabilistic
handler has type:

```text
H : (op : Σ.Op) → S → PMF (Execution S E (Σ.Reply op)).
```

Its execution is [monadic execution](../core/execution.md#outer-effects)
with outer monad `PMF`. A stopping operation returns mass on its actual
`stopped` result, residual state and events. Sequencing preserves that record
and does not invoke its continuation. A returning operation passes its actual
reply and residual state to the continuation and appends the resulting events.
This defines a normalized distribution for every finite reply-adaptive body.

An arbitrary outer monad has no such probability interpretation merely because
it satisfies monad laws. In particular, an outer exception with no execution
record supplies neither a stopped record nor its residual state and events.
A selected subdistribution semantics specifies what missing mass means, such
as divergence, and how the claimed observer handles it. It is a separate
interpretation; the normalized profile does not discard unsuccessful runs or
renormalize successful ones.

## Joint initialization and persistence

Let `Z` contain the complete initially sampled configuration: setup, actual
role inputs, private state and coins, correlated resources, and provider state.
Let `ι : PMF Z` be its joint law, `initial : Z → S` its runtime-state map, and
`body(z) : Proc Σ A` the body selected from that configuration. For a possibly
configuration-dependent handler `H(z)`, the initialized result law is:

```text
bind(ι, z ↦ runM(H(z), body(z), initial(z))).
```

Source and statement selection obey the information boundary fixed by the
experiment. Sampling all private data into `Z` does not grant a strategy access
to all of `Z`. A hidden future tape can be part of initialization without being
an input to source selection or local operations.

Every subsequent call consumes the actual successor state of the preceding
call. Correlations between setup, local state, provider state and previous
outputs remain in that state and its reached distribution. An independence
claim for random variables `f(z)` and `g(z)` means that their actual joint
law factors into the product of their marginals. Separate names, storage
objects or native random-generator calls do not establish this equality.

The [product-tape profile](../profiles/providers/product-tapes.md#interface-and-product-initialization)
selects a conditional product suffix. The
[correlated-service profile](../profiles/services/affine.md#joint-service-coupling-and-its-observer)
instead uses a specified correlated law and observation-preserving change of
samples. Neither interpretation is a default for an arbitrary provider.

## Reached views and finite masses

Let `V` be the strategy's complete pre-draw view, `H` the remaining hidden
state, and `D` the successful output type. The view includes every input that
may affect the next decision: permitted setup, replies, private controller
memory and coins already available, and the selected request. Let `H` be
finite, and define the rational functions:

```text
μ : V → H → ℚ
K : V → H → D → H → ℚ

viewMass(v)     = Σh μ(v,h)
outputMass(v,d) = Σh Σh' μ(v,h) K(v,h,d,h')
update(v,d,h')  = Σh μ(v,h) K(v,h,d,h').
```

`μ` is the actual joint reached mass, before normalization at a particular
view. `K` is the successful-output transition, including successor hidden
state. A probability interpretation requires nonnegative masses. When these
functions represent a reached portion of a normalized experiment, the total
mass of `μ` is at most one, and each row of `K` has mass at most one. Sums over
`V` or `D` in the finite rational profile additionally require those types to
be finite. The algebraic definitions themselves only sum over finite `H`.

The update marginal is exact:

```text
Σh' update(v,d,h') = outputMass(v,d).
```

When `viewMass(v) > 0`, the conditional probability of a successful output `d`
at that view is `outputMass(v,d) / viewMass(v)`. It is not conditioned on the
provider succeeding. Hidden states are weighted by the actual posterior
`μ(v,h) / viewMass(v)`, not by the original seed distribution. A zero-mass
view has no conditional probability supplied by this division rule.

If every row of `K` has total mass one, then:

```text
Σd outputMass(v,d) = viewMass(v).
```

This normalization premise describes a complete-output kernel. A kernel
containing only successful outputs generally fails it when the provider can
stop. Rational mass identities and inequalities can be valid without
nonnegativity or normalization; that weaker algebra alone is not a probability
claim.

## Point caps and information

For `ε : V → ℚ`, define:

```text
JointCap(μ,K,ε) :=
  ∀ v d, outputMass(v,d) ≤ ε(v) * viewMass(v).
```

For probability use, `ε` is nonnegative. The cap implies, at every positive-mass
view:

```text
outputMass(v,d) / viewMass(v) ≤ ε(v).
```

The stronger factorization
`outputMass(v,d) = viewMass(v) * ν(v,d)` gives conditional mass `ν(v,d)`.
The function `ν` is a full output distribution only when the corresponding
successful transition has full mass.

A statewise bound `Σh' K(v,h,d,h') ≤ ε(v)` is sufficient for `JointCap` when
`μ` is nonnegative. It is not necessary: fixing a hidden tape may make its
next output deterministic while the posterior mixture still has a useful cap.

Caps survive forgetting information in the following direction. For finite
`V`, a map `f : V → W`, a constant cap `ε`, and each `w,d`:

```text
Σv [f(v)=w] outputMass(v,d) ≤ ε * Σv [f(v)=w] viewMass(v).
```

For a varying cap, the right side obtained by summation is instead
`Σv [f(v)=w] ε(v) * viewMass(v)`. A claimed cap depending only on `w` needs an
appropriate bound on this quantity. A bound for a coarser view does not imply
the same bound for a more informative view.

*Example (informative).* For independent uniform bits `a,b`, observing either
`a` alone or setup `a xor b` alone leaves `b` uniform. Observing both determines
`b`. Separate marginal information checks therefore miss the actual joint
view available to the strategy.

## Adaptive events and complete updates

Let `bad : V → Finset D` select a finite bad set before the draw, and let
`active : V → Bool` decide whether to request. A point cap gives:

```text
Σd∈bad(v) outputMass(v,d) ≤ |bad(v)| * ε(v) * viewMass(v)

Σv [active(v)] Σd∈bad(v) outputMass(v,d)
  ≤ Σv [active(v)] |bad(v)| * ε(v) * viewMass(v).
```

The second sum requires finite `V` in this rational presentation. The selected
set and decision can adapt to the whole pre-draw view, but not to the output
being bounded. A consumer can impose additional conditions on successful
outputs; using the displayed bound then requires its accepting event to be
contained in the selected bad-output event. Stopped or declined fibers do not
count as successful outputs unless the consumer defines a different event.

The output-indexed `update` above is not a complete history updater by itself.
For a finite complete transition, let `L` encode all newly visible emissions
and let `Z = Outcome D × L`. Supply nonnegative normalized rows:

```text
T : V → H → Z → H → ℚ
Σz,h' T(v,h,z,h') = 1

K(v,h,d,h') = Σℓ T(v,h,(returned d,ℓ),h').
```

Let `advance : V → Z → Vnext` be the actual next-view update, including the
observed status, emissions and controller-memory changes represented by this
transition. Then the complete successor joint mass is:

```text
μnext(v',h') = Σv,h,z [advance(v,z)=v'] μ(v,h) T(v,h,z,h').
```

All random choices affecting the update are included in the transition's
state or emitted record. This equation retains total reached mass, including
stops, by summing normalized rows and routing each record to exactly one next
view. A profile with more detailed observations uses the corresponding `Z`;
it cannot erase those observations and still claim a cap for the full view.
Continuing an enclosing controller after an inner stop is an explicit
experiment transition, not an invocation of the stopped body's continuation.

## Attempts and extensions

A sequence of attempts uses the enclosing experiment's actual residual state
and retry rule. A per-attempt bound does not by itself bound the distribution
conditioned on eventual success. For finitely many bad-attempt events `Bᵢ` in
one experiment, event inclusion gives the ordinary bound
`Pr[⋃ᵢ Bᵢ] ≤ Σᵢ Pr[Bᵢ]`; independence is unnecessary, but each term concerns
that same enclosing law. A bound proved after resetting a provider applies
only if the selected experiment actually performs and justifies that reset.

Computational, pseudorandom-generator, Fiat–Shamir, fixed-oracle and quantum-oracle
claims select their own initialization, access, strategy and comparison/loss
laws. Deterministic construction preservation or a product-tape equality does
not identify those experiments. A different probability library is compatible
when its actual distributions, execution and consumer probabilities correspond
to the selected claim.

## Iteration, complete transitions and production loss

For a finite input index `x` with mass `mu x` and normalized transition kernel
`K x d`, let `record x d` contain the actual outcome, residual state and events.
A next-view map sees that whole record, including stops. Its pushforward mass is
`sum x,d: nextView x (record x d) = v, mu x * K x d`. Summing over all `v`
retains the original total mass. Filtering to success before this update is a
different, conditional experiment.

For any Boolean event on the next view, summing its pushed-forward mass equals
summing `mu x * K x d` over exactly the complete records satisfying that event.
This supports queries of pending, stopped or published outcomes. It is a
one-step identity, not a theorem that the chosen next view is sufficient state
for another transition. Reusing a reduced state requires its next transition law
to factor through that view, or retention of the actual posterior hidden state.
Two equal current observations can have different next-output distributions.
Choosing a representative hidden state or restoring the original prior is not
justified by mass conservation.

For an [iterated producer](../core/iteration.md), let `pending n` be the mass
still requesting another attempt. If the actual reached-history law establishes
`pending (n+1) <= q * pending n`, with `q >= 0`, then
`pending n <= q^n * pending 0`. A bound on marginal retry probability alone
is insufficient: reusing one hidden fair bit makes every marginal retry
probability one half, but all-retry probability stays one half at every horizon.
Independence is sufficient in appropriate models, not necessary when the
history-conditional bound is proved directly.

An accepted-publication lower bound additionally needs a partition into accepted,
pending and lost mass. Lost mass includes fatal execution and publication failure.
This is distinct from target-constraint satisfiability. An infinite-controller
claim needs a justified limit/subdistribution or measure construction; the finite
mass and prefix theorems do not supply one. Nor do uniform full-field batch-weight
bounds automatically apply to sampling conditioned on nonzero values.
