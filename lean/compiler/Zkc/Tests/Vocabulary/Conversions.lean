import Zkc.Tests.Vocabulary.Outcome

/-!
Conformance cases of conversions by a fact to `nonzero<F>` and to an `index<s>` that a row takes:
the frontend applies `field.nonzero` or `nat.below` where the narrower type is expected (TY5,
§7.4), and the core decides it.
-/

namespace Zkc.Vocabulary.Cases.Conversions

open Zkc.Core Zkc.Vocabulary.Cases

/-- A row of bls12-381.fr, the scalar field of `G1`, at all its elements and at those that are not
zero. -/
abbrev frRow (r : Zkc.Vocabulary.FieldRow) : Raw := .row (.field r .bls12381Fr .all)
abbrev frNz (r : Zkc.Vocabulary.FieldRow) : Raw := .row (.field r .bls12381Fr .nonzero)

/-- `Schnorr<G>::Run`, modelled as a record of the two fields that the function reads:
`challenge` (position 0) and `response` (position 1); `Runs<k>` is `[Run; k]` (§8). -/
abbrev runTy : Ty := .record ⟨90⟩ false (.cons Fr (.cons Fr .nil))

/-- `response_difference<G = g1>` of `examples/schnorr.zkc` at `Runs<k>`:
`gap = runs[0].challenge - runs[1].challenge; guard gap != 0;
return (runs[0].response - runs[1].response) / gap`. `/` by `gap` is `field.nonzero(gap)` (a
conversion by a fact), `field.inverse` at the nonzero elements, `field.from_nonzero` and
`field.mul`; `gap != 0` is `field.is_nonzero(gap)` (§7.4). -/
def respDiff (k : Nat) (guarded : Bool) := check [G1, G1, sized runTy k] [Fr] guarded <|
  .mk [0, 1, 2] ([
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (item (sized runTy k)) [2, 10],
    .op ⟨3⟩ [12] (get runTy 0) [11],
    .op ⟨4⟩ [13] (natural 1) [],
    .op ⟨5⟩ [14] (item (sized runTy k)) [2, 13],
    .op ⟨6⟩ [15] (get runTy 0) [14],
    .op ⟨7⟩ [16] (frRow .sub) [12, 15]] ++
    (if guarded then [
      .op ⟨8⟩ [17] (frRow .isNonzero) [16],
      .guard ⟨9⟩ () 17 .reject] else []) ++ [
    .op ⟨10⟩ [18] (get runTy 1) [11],
    .op ⟨11⟩ [19] (get runTy 1) [14],
    .op ⟨12⟩ [20] (frRow .sub) [18, 19],
    .op ⟨13⟩ [21] (frRow .nonzero) [16],
    .op ⟨14⟩ [22] (frNz .inverse) [21],
    .op ⟨15⟩ [23] (frNz .fromNonzero) [22],
    .op ⟨16⟩ [24] (frRow .mul) [20, 23]]) [24]

/-- `M-SCH2`: without `guard gap != 0` (the body then cannot stop). -/
def «M-SCH2» := respDiff 2 false
/-- `M-SCH13`: `Runs<1>`, with the guard. -/
def «M-SCH13» := respDiff 1 true
/-- `L-SEQ5` at `batch_inverse<F, n>`: `[x - x for x in values]` where `[nonzero<F>; n]` is
expected: `x - x` is an `F` (TY6), converted by `field.nonzero`. -/
def «L-SEQ5» (n : Nat) := check [sized Fnz n] [sized Fnz n] false <| .mk [0] [
  .loop ⟨1⟩ () (.fixed n) [] [10]
    (.mk [20] [
      .op ⟨2⟩ [21] (item (sized Fnz n)) [0, 20],
      .op ⟨3⟩ [22] (nzrow .fromNonzero) [21],
      .op ⟨4⟩ [23] (nzrow .fromNonzero) [21],
      .op ⟨5⟩ [24] (frow .sub) [22, 23],
      .op ⟨6⟩ [25] (frow .nonzero) [24]] [25])] [10]

/-- `L-COS1` at `at<F = koala-bear, k>`: `domain.shift * F::root(k + 1) ^ i`. `root` takes an
`index<TwoAdicity + 1>`, `index<25>` at koala-bear; `k + 1` is a static term, written as the
number it evaluates to and converted by `nat.below` (TY2, TY5). -/
def «L-COS1» (k : Nat) := check [cosetTy, .fin (2 ^ k)] [Fnz] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (get cosetTy 0) [0],
  .op ⟨2⟩ [11] (natural (k + 1)) [],
  .op ⟨3⟩ [12] (narrowTo 25) [11],
  .op ⟨4⟩ [13] (frow .root) [12],
  .op ⟨5⟩ [14] (toNat (2 ^ k)) [1],
  .op ⟨6⟩ [15] (nzrow .pow) [13, 14],
  .op ⟨7⟩ [16] (nzrow .mul) [10, 15]] [16]

/-- `L-COS2` at `interpolate<F = koala-bear, k>`:
`[(∑ i ∈ 0..2^k, values[i] / values[i] ^ j) / 2^k for j in 0..2^k]`. The inner sum collects its
terms and applies `seq.sum`; `values[i] ^ j` is an `F`, converted by `field.nonzero` where `/`
needs a `nonzero<F>`; `2^k` is a literal of `nonzero<F>` (TY6). -/
def «L-COS2» (k : Nat) :=
  let n := 2 ^ k
  check [sized F n, cosetTy] [sized F n] false <| .mk [0, 1] [
    .loop ⟨1⟩ () (.fixed n) [] [10]
      (.mk [20] [
        .loop ⟨2⟩ () (.fixed n) [] [21]
          (.mk [30] [
            .op ⟨3⟩ [31] (item (sized F n)) [0, 30],
            .op ⟨4⟩ [32] (item (sized F n)) [0, 30],
            .op ⟨5⟩ [33] (frow .pow) [32, 20],
            .op ⟨6⟩ [34] (frow .nonzero) [33],
            .op ⟨7⟩ [35] (nzrow .inverse) [34],
            .op ⟨8⟩ [36] (nzrow .fromNonzero) [35],
            .op ⟨9⟩ [37] (frow .mul) [31, 36]] [37]),
        .op ⟨10⟩ [22] (sumRow (some n)) [21],
        .op ⟨11⟩ [23] (unit n) [],
        .op ⟨12⟩ [24] (nzrow .inverse) [23],
        .op ⟨13⟩ [25] (nzrow .fromNonzero) [24],
        .op ⟨14⟩ [26] (frow .mul) [22, 25]] [26])] [10]

example : «M-SCH2» = .refused [unjustified 13 (frRow .nonzero)
    (.holds (.apply (frRow .isNonzero) [0])) [none]] := by
  decide +kernel
example : «M-SCH13» = .refused [unjustified 5 (item (sized runTy 1))
    (.below (.arg 1) 1) [pt 1]] := by
  decide +kernel
example : «L-SEQ5» 0 = .accepted [] := by decide +kernel
example : «L-SEQ5» 1 = .refused [unjustified 6 (frow .nonzero)
    (.holds (.apply (frow .isNonzero) [0])) [none]] := by
  decide +kernel
example : «L-COS1» 24 = .refused [unjustified 3 (narrowTo 25) (.below (.arg 0) 25) [pt 25]] := by
  decide +kernel
example : «L-COS1» 0 = .accepted [] := by decide +kernel
example : «L-COS1» 3 = .accepted [] := by decide +kernel
example : «L-COS2» 0 = .refused [unjustified 6 (frow .nonzero)
    (.holds (.apply (frow .isNonzero) [0])) [none]] := by
  decide +kernel
example : «L-COS2» 1 = .refused [unjustified 6 (frow .nonzero)
    (.holds (.apply (frow .isNonzero) [0])) [none]] := by
  decide +kernel

end Zkc.Vocabulary.Cases.Conversions
