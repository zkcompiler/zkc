# Independent STARK mathematical components

`ZkcSecurity.Families.Stark` owns polynomial mathematics over a field `F`.
Evaluation domains are embeddings `Index ↪ F`; answer vectors are functions
on actual finite point sets. These components do not define native/shared
formats, readers, a STARK verifier, or a separate FRI implementation.

## Constraint quotient and batching

`vanishes_iff_exists_quotient` in `Families.Stark.Quotient` says that a polynomial of degree below
`d` vanishes on a finite set `S` exactly when it is `V_S * q` with
`q.degree < d - |S|`. Here `V_S` is Mathlib's monic Lagrange nodal polynomial.
The strict degree convention includes the zero polynomial at budget zero.
The existing `Families.Polynomial.Quotient` separately owns the claim-relation
interface with a non-strict natural-degree budget.

`powerBatch` in `Families.Stark.Batching` is `∑ i < m, α^i * p_i`. If some fixed `p_i` is nonzero,
`powerBatch_zero_uniform_le` bounds the probability of a zero polynomial batch
by `(m - 1) / |F|` for a uniform field challenge. It extracts a nonzero
coefficient and uses the existing univariate root bound. This theorem does not
assert proximity preservation for an adaptively selected low-degree target.

`constraint_test_uniform_le` in `Families.Stark.ConstraintBatching` additionally samples an
independent uniform evaluation point from a nonempty finite set `T`. If every
residual polynomial has natural degree at most `D`, its zero-evaluation
probability is at most `(m - 1) / |F| + D / |T|`.
The theorem's `SampleableType` premises specify uniform laws, rather than
arbitrary sampler implementations. A protocol client must establish those laws
after conditioning on its reached history.

For quotient claims the residual is `p - V_S * q`. Its natural degree is at
most `max p.natDegree (|S| + q.natDegree)`. A numerator degree check alone does
not justify a residual bound. `powerBatch_residual` proves the exact common-set
quotient/batch equation.

`multivariate_zero_uniform_le` reuses Mathlib's Schwartz–Zippel theorem with
the **total degree** and a uniform product draw. An individual-variable degree
bound needs a separately justified total-degree bound; it cannot be substituted
directly in the numerator.

## Out-of-domain sampling

`outsidePoints` in `Families.Stark.OutOfDomain` is `F \ domain(Index)`. Its cardinality is exactly
`|F| - |Index|`, and it is nonempty exactly when `|Index| < |F|`.
`outside_agreement_uniform_le` bounds agreement of two distinct degree-below-`d`
polynomials at a uniform point of this typed complement by
`(d - 1) / (|F| - |Index|)`.
`outside_error_lt_one` exposes the field-size inequality required for a
nontrivial error bound. Bounds at least one are permitted mathematical bounds,
without being useful parameter certificates.

The optional `ZkcArkLib.Stark.list_collision_le` in `Stark.OutOfDomain` applies the pinned
ArkLib `OutOfDomSmpl.out_of_dom_smpl_1` to its exact collision event: two distinct
nearby Reed–Solomon codewords agree at every independently sampled OOD point.
Its bound is
`L(L - 1)/2 * ((d - 1)/(|F| - |Index|))^samples`, with explicit list-decodability,
radius, list-size and nonempty-complement premises. Repeated samples are allowed.

## DEEP quotient and batching

`deepQuotient S p` subtracts the interpolant of the true evaluations of `p`
on `S`, then uses Mathlib's monic division by `V_S`. Reconstruction, off-set
evaluation and degree-below-`d - |S|` laws are proved. `deepQuotient_powerBatch`
proves that this operation commutes with batching on the same set. The degree
reduction uses the number of **distinct points**, not the number of draws.
`lift_answers` and `lift_agreement` recover claimed point values and off-set
agreement, respectively.

The optional `ZkcArkLib.Stark.Quotient` proves exact representation equalities
with ArkLib's `vanishingPoly`, `ansPoly` and `polyQuotient`.
`quotient_distance_gt` applies its proved `Quotienting.quotienting` theorem:
if every codeword within radius `δ` disagrees with a claimed answer on `S`,
then the quotient word is farther than `δ` from degree-below-`d - |S|` codewords.
It requires `|S| < d ≤ |Index|` and disjointness of `S` from the evaluation
domain. Disjointness removes the upstream in-domain fill/disagreement loss.

`ZkcArkLib.Stark.affine_jointAgreement` in `Stark.DeepBatching` is a proved restricted
proximity seam for **two fixed words**, combined as `u₀ + α u₁`, with a common
target degree. At a radius at most the code's relative unique-decoding radius,
a close-combination probability greater than `|Index| / |F|` forces both words
to agree with codewords on one common set of at least `(1 - δ)|Index|` positions.
The root is ArkLib's proved affine-line joint-agreement theorem.

The same module also proves **many-word power batching with a common target
code**, using the independent, proved capacity bound
`CodingTheory.linear_mcaError_powers_le`. Let `n = |Index|`, `q = |F|`, and let
`words : Fin (k + 1) → Index → F` and `C : LinearCode Index F` be fixed before
drawing gamma uniformly from `F`. The actual batch is
`i ↦ ∑ j, gamma^j * words j i`. `powerBatch_distance_uniform_le` proves

```text
Pr[dist(batch, C) ≤ δ ∧ ∃ j, δ < dist(words j, C)] ≤ powerBatchError n q k Δ η
```

The assumptions are `1 ≤ k`, `k + 1 ≤ q`, exact normalized minimum distance
`Δ = Code.minDist C / n`, `0 < η < Δ`, and
`0 ≤ δ ≤ 1 - (1 - Δ + η)^(1/(k + 2))`. Radii, slack and minimum distance are
`NNReal`; the size and radius inequalities use their real casts. With
`a = 1 - Δ + η`, the explicit `ENNReal` error definition is

```text
ENNReal.ofReal (
  n * (1 - a^(1/(k+1))) / η * (k/q)
  + max (2*k / (η * (a^(1/(k+2)) - a^(1/(k+1))) * q))
        ((k+1)*(k+2) / (η*q)))
```

`powerBatch_bad_implies_isMCA` constructs the MCA agreement-set witness from a
closest codeword to the batch: a far input cannot have a codeword extension on
that same sufficiently large set. Probability monotonicity and the pointwise
supremum inequality then reduce the distance event to the exact upstream bound.
`powerBatch_distance_gt_of_not_isMCA` states the useful pointwise implication:
outside the MCA event, one far input forces the batch to be farther than `δ`.
`powerBatch_close_uniform_le` bounds the close-batch event when the caller
already supplies a far input. The fixed family and common code do not depend
on gamma; a protocol client must establish uniformity after its prior history.

`quotient_powerBatch_close_uniform_le` connects actual quotient values to this
bound. Its typed parameters are original words, `points : Fin (k + 1) → Finset F`
and `answers : ∀ j, points j → F`. Every set is outside `domain`, every set has
the same cardinality `removed`, and `removed < degree ≤ n`. The batch inputs are

```text
i ↦ (words j i - interpolate(points j, answers j)(domain i)) / V_(points j)(domain i)
```

and the common target is exactly `RS(domain, degree - removed)`. If one original
word has the answer-disagreement premise of `quotient_distance_gt`, that theorem
supplies a far quotient input and the close quotient-batch probability has the
same error. The answer sets may differ; their common cardinality and the target
code are explicit. Minimum distance and the radius gate refer to this reduced
code. This neither requires honest input words nor asserts their proximity.

This proved range shrinks with the number of words. For a nonzero RS target
degree `d ≤ n`, its minimum distance is `n - d + 1`, so the radius gate is
`δ ≤ 1 - ((d - 1)/n + η)^(1/(k + 2))`. A desired radius exceeding this threshold
is outside the theorem's scope even if a larger-radius FRI theorem is available.
No flagship parameter suite or error below one is certified here. The native
single-table STARK uses this one-gamma power pattern for its fixed quotient
words; associating its actual values, target and conditional challenge law with
these typed parameters remains a client correspondence obligation.

The pinned general `Combine.combine_theorem` transitively uses `sorryAx` through
`ProximityGap.correlatedAgreement_affine_curves`. It is inspected in
`TestsArkLib.StarkUpstreamAudit` and is not an established dependency of these
adapters. General degree-corrected STIR combination remains open. The established
many-word result above uses one common code and its stated restricted radius.

## Validation and composition boundary

`TestsSecurity.Stark` includes kernel-checked controls over `ZMod 3`: a nonzero
`X^3 - X` vanishes everywhere; `X₀ X₁` vanishes on five of nine points despite
individual degree one; an oversized quotient increases the residual degree;
full-field domains have empty complements; and strict zero budgets retain zero.
`TestsArkLib.Stark` checks three-word cancellation with a far input, its MCA
witness and an actual probability-bound instantiation. It refuses too many
words for the field, zero slack, a false minimum distance and radius one.
The small-field bound is not presented as a nontrivial numerical error estimate.
The focused axiom tests inspect the transitive closures of all new roots and
the upstream results actually reused. Allowed axioms are `propext`,
`Classical.choice` and `Quot.sound`.

An actual STARK client still needs its AIR encoding/adequacy theorem, selected
degree and field-size admissions, causal challenge laws, exact committed first
layer and quotient values, and composition with the single FRI component and
Merkle/Fiat–Shamir realization. IR owns native/shared formats; the Lean client owns the source/candidate
association. These components do not supply that correspondence, certify a
parameter suite, or establish bounded-search provider correspondence.
