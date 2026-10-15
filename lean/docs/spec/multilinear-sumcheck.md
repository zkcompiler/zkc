# Multilinear Sumcheck mathematics

`Zkc.Protocols.Sumcheck.Multilinear` is an independent mathematical foundation
for the scalar multilinear library in
[`libraries/sumcheck/lib.zkc`](../../../libraries/sumcheck/lib.zkc).
It models endpoint messages, ordered table restriction, residual truth and
complete public-table discharge. It does not import this source, define its
open process, or establish native correspondence or interactive security.
The existing quadratic Sumcheck and factor-opening contracts remain separate.

## Representation and modules

| Module | Owned interface |
|---|---|
| `Zkc.Polynomial.Multilinear.Restriction` | Existing `Table`, ordered `half` and `booleanSum`, `fixFirst`, exact-length `ofList?`, extension and vector-sum laws |
| `Zkc.Polynomial.Multilinear.Prefix` | `fixPrefix`, ordered extension and remaining-sum laws, complete restriction |
| `Zkc.Protocols.Sumcheck.Multilinear.Round` | `Message = F × F`, `boundary`, `evaluate`, `honestMessage`, explicit delivery laws |
| `Zkc.Protocols.Sumcheck.Multilinear.Reduction` | `ResidualClaim`, mathematical `check`, complete discharge and public-input agreement |

`Table F n` is the existing function `(Fin n → Bool) → F`. Its first coordinate
is the most significant bit of the existing `index`. A low half fixes that
coordinate to `false`; a high half fixes it to `true`. `ofVector`, `vertex`, and
`extension` retain their original meanings. There is no second indexing scheme
or conversion to the quadratic security model.

`fixFirst : Table F (n+1) → F → Table F n` enforces residual shape intrinsically.
For tail vertex `b`, it returns `(1-r)*T(false::b) + r*T(true::b)`.
`fixFirst_apply` proves equality to the source helper's
`low + (high-low)*r`. `fixFirst_zero` and `fixFirst_one` select the two halves.

`fixPrefix k : Table F (n+k) → (Fin k → F) → Table F n` consumes the point
from first coordinate to last. `Quadratic.point` is reused solely as the
existing generic coordinate concatenation operation: its `k` coordinates come
before the `n` suffix coordinates, despite the arity being written `n+k`.
`extension_fixPrefix_coordinates` identifies this operation with list append
under explicit list-length hypotheses. No point is reversed for storage layout.
The `0+k` in completion signatures retains this dependent arity convention;
clients may normalize it with `Nat.zero_add`.

The optional raw adapter `ofList? n values` succeeds exactly when
`values.length = 2^n`. `ofList?_entry` relates each decoded vertex to an actual
list lookup, and `booleanSum_ofList?` identifies its sum with `List.sum`.
It neither pads nor truncates. This is a scalar mathematical shape check:
source dimensions below 64, positive column width, checked machine indices,
allocation limits, and repeat bounds are separate native premises.

## Laws and assumptions

Shape and lookup laws need no algebra. `boundary_honestMessage` needs addition.
`booleanSum_eq_sum` and `booleanSum_ofVector` require an additive commutative
monoid; `booleanSum_add` needs only an additive commutative semigroup, and
`booleanSum_scale` a nonunital nonassociative semiring. Restriction, endpoint
evaluation and honest update use a ring, including noncommutative rings.
The equivalence to the source's right-multiplication helper and the extension
laws use a commutative ring, matching the existing `extension` assumption.
The executable mathematical checker additionally needs decidable equality.
No foundation theorem requires a finite field, characteristic bound or sampling.

For the honest endpoint pair `a = honestMessage T`:

```text
boundary a = sum(T)
evaluate a 0 = a.1
evaluate a 1 = a.2
evaluate a r = (1-r)*a.1 + r*a.2 = sum(fixFirst T r)
extension (fixFirst T r) x = extension T (r :: x)
extension (fixPrefix k T p) x = extension T (p ++ x)
```

The exact exported results are `boundary_honestMessage`, `evaluate_zero`,
`evaluate_one`, `evaluate_honestMessage`, `extension_fixFirst`, and
`extension_fixPrefix`. Endpoint pairs are not coefficient pairs:
`evaluate_affine` gives `a.1 + r*(a.2-a.1)`.

`ResidualClaim k T p c` means `booleanSum (fixPrefix k T p) = c`.
`residualClaim_iff` identifies it with the Boolean sum of the original extension
at points beginning with `p`. When the remaining dimension is zero,
`residualClaim_complete_iff` identifies it with one full evaluation.
`fixPrefix_complete` supplies the corresponding singleton-table equation.
Zero rounds leave the table and claim unchanged (`fixPrefix_zero`,
`residualClaim_zero`); they do not complete a table with positive dimension.

`check values point claim` checks exact scalar shape and compares the extension
at the full point with the claim. `check_eq_true_iff` exposes both premises.
`check_complete_iff` proves that this check is equivalent to the complete
residual computation. `check_zero_iff` states exactly that an empty-point check
accepts if and only if `values = [claim]`. This pure checker uses the proved
extension equation; it does not model the source's staged computation or stops.

## Role-local contracts and the execution boundary

`role_local_update` keeps the delivered pair and two challenges explicit. If
the received pair is the honest pair, then

```text
sum(fixFirst T cp) - evaluate received cv = (cp-cv)*(a.2-a.1).
```

`honest_update` requires both message equality and `cp = cv` explicitly.
It does not assume unequal challenges always give unequal values: a constant
round can agree. `check_of_residual` separately requires equality of the two
public tables and equality of the ordered role-local points. Its common field
type and typed arity presuppose field identity and agreed dimension/count; native availability annotations do
not supply those agreements. A malicious-prover security consumer should bind
the verifier's fixed statement, rather than assume an adversary's table agrees.

The pair algebra accepts arbitrary pair values. There is no process constructor
that silently makes received values equal to sent values. A later `PIR.Proc`
contract must preserve the source order: receive both endpoints, guard the
boundary, draw `cv`, deliver a separate `cp`, and update each role locally.
The actual lowering uses two ordered scalar receives for the pair. Keep both
in the source-facing contract, including the intermediate state and possible
stops. A strategy or handler may aggregate them into an endpoint pair through
an explicit correspondence lemma; atomic receipt is not the same effect tree.

The independent process package must also retain local count checks, maximum
failure distinct from authored rejection, the original table guards, ordered
point appends, service identity and successor state. Full source import still
needs vector split/sum/map, shape/index arithmetic, helper composition, folds,
open operations and repetition. No whole-Sumcheck kernel is assumed here.

## Next optional integration

The owning optional manifest pins ArkLib
`db7005f84a9dbad7ff2abbbb4e8feeeac6f4dfd8` and VCVio
`d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0`. Core imports remain independent.
The next package should:

1. Map `Message F` to `C a0 + C (a1-a0) * X`, prove degree at most one,
   pointwise evaluation equality using `evaluate_affine`, and Boolean boundary
   equality using `evaluate_zero`/`evaluate_one`. This needs no division by two.
2. Realize `Table F N` using ArkLib's `MvPolynomial.MLE` on explicitly converted
   Boolean assignments. Prove agreement with `extension`, `booleanSum`, and
   prefix restriction. Do not assume `MLE'`'s flat-index convention matches
   this package's MSB order. `MLE_mem_restrictDegree` supplies the upstream
   per-coordinate degree-one fact once the realization is connected.
3. Instantiate `Sumcheck.Interaction.Native.Core` with `M = F × F` and this
   `evaluate`. `Core.execute_transport` in `Interaction/Protocol.lean:290–303`
   requires pointwise evaluation equality and equality of original-oracle
   views. It retains arbitrary effectful prover continuations, including the
   response to public abort. Connect the selected acceptance event through the
   forthcoming `PIR.Proc` interface; do not equate unlike raw traces.
4. Apply `Native.execute_soundness` in
   `Interaction/ProtocolSoundness.lean:201–214` only after those connections.
   It requires `[Field F] [Fintype F] [DecidableEq F] [SampleableType F]`, an
   injective Boolean domain, a fixed realized degree-bounded original oracle,
   a false initial relation, `start + count = N`, and the actual causal prover
   strategy with reached fresh uniform challenges. Setting degree one gives
   `count / |F|`. Partial reduction needs a separate induction using
   `MultivariateRound.uniform_successor_soundness` (:40–49); the full theorem
   alone is not a partial-reduction result.

None of these security connections is a theorem of this foundation package.

## Regression coverage

`Tests.MultilinearSumcheck` is included in the full core declaration audit and
Lake test library. It checks endpoint/coefficient confusion, pair reversal,
MSB coordinate order, incomplete versus complete obligations, unequal role
points, unequal public tables, exact shape and zero rounds. A standalone client
in `clients/Main.lean` consumes the arbitrary-dimensional residual theorem.

The early-challenge control proves over any field, for `2*r-1 ≠ 0`, that
`(r/(2*r-1), (r-1)/(2*r-1))` has boundary one and evaluates to zero at `r`.
Over F97 the excluded challenge is exactly 49; any boundary-one pair evaluates
to 49 at that exceptional challenge. Thus a pair chosen after learning the
challenge can falsify the intended zero-table claim at every other challenge.
This is an algebraic counterexample to a misplaced ordering premise, not a
finite security proof. Concrete checks use kernel reduction (`decide +kernel`),
and general laws use ordinary proof terms; no native decision axiom is used.
