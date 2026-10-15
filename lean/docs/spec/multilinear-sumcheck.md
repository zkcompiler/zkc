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
| `Zkc.Polynomial.Multilinear.Marginal` | `sumRemaining`, total preservation, commutation with restriction, extension as residual sum |
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

`sumRemaining n k table` retains the first `k` Boolean coordinates and sums
the remaining `n` coordinates using the existing concatenation. Its total
equals the original total (`booleanSum_sumRemaining`, requiring only addition).
`fixFirst_sumRemaining` commutes with restriction over a ring, and
`extension_sumRemaining` identifies its extension at `point` with
`booleanSum (fixPrefix k table point)` over a commutative ring. The round law
`honestMessage_sumRemaining` preserves the endpoint pair using only addition.
These are core table laws; no security backend is required.

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

## Optional integration and next source seam

The [optional multilinear security package](multilinear-sumcheck-security.md)
now proves the degree-one endpoint interpretation, explicit Boolean-assignment
MLE/table agreement, ordered restriction and table-oracle realization. It uses
ArkLib `Native.Core.execute_transport` with arbitrary effectful continuations
and public abort, then applies `Native.execute_soundness` for the complete
`N / |F|` bound. Honest completeness allows arbitrary challenges. A proved
marginal table gives partial residual soundness `k / |F|` without a new partial
executor or padding the challenge point. These security results belong to the
optional package; core imports remain dependency independent.

The owning optional manifest pins ArkLib
`db7005f84a9dbad7ff2abbbb4e8feeeac6f4dfd8` and VCVio
`d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0`. Its exact quantitative assumptions and
oracle/observation boundaries are specified in the linked document.

The remaining source seam is an explicit `PIR.Proc` contract and handler theorem
for the actual two ordered scalar receives, boundary guard, reached fresh
challenge, role-local delivery, counts and stops. The selected observation must
agree with the optional experiment; unlike raw traces must not be equated.
This foundation and its optional consumer do not establish that correspondence.

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
