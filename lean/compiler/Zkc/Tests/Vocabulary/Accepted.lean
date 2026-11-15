import Zkc.Tests.Vocabulary.Outcome

/-!
Accepted cases of other rules (FN5, SP3, SP12, NL6) whose functions apply operations with a
domain: their verdict is the frontend's rule, and the core must accept what the frontend emits.
-/

namespace Zkc.Vocabulary.Cases.Accepted

open Zkc.Core Zkc.Vocabulary.Cases

/-- `R-FN5a`: `dot(a: [F; 4], b: [F; 4]) -> F: ∑ i ∈ 0..4, a[i] * b[i]`. -/
def «R-FN5a» := check [sized F 4, sized F 4] [F] false <| .mk [0, 1] [
  .loop ⟨1⟩ () (.fixed 4) [] [10]
    (.mk [20] [
      .op ⟨2⟩ [21] (item (sized F 4)) [0, 20],
      .op ⟨3⟩ [22] (item (sized F 4)) [1, 20],
      .op ⟨4⟩ [23] (frow .mul) [21, 22]] [23]),
  .op ⟨5⟩ [11] (sumRow (some 4)) [10]] [11]

/-- `N-SP3b`: `parity(x: F) -> nat: F::to_nat(x) % 2` (`to_nat` gives an `index<Order>`). -/
def «N-SP3b» := check [F] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (frow .toNat) [0],
  .op ⟨2⟩ [11] (toNat 2130706433) [10],
  .op ⟨3⟩ [12] (natural 2) [],
  .op ⟨4⟩ [13] remainder [11, 12]] [13]

/-- `Naturals::add` and `Naturals::zero`, with `T = nat`. -/
def addHeader (key : Nat) : FnHeader V := ⟨⟨key⟩, [.nat, .nat], [.nat], false, none⟩
def zeroHeader (key : Nat) : FnHeader V := ⟨⟨key⟩, [], [.nat], false, none⟩
def «Naturals-add» := run [] (addHeader 1) (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10])

/-- `N-SP12h` at `ends<X = Naturals, n>`: `pair = (xs[0], xs[n]); return (pair.0 + pair.1,
pair.1)`, `+` on `X::T` the member `add` (NL6). -/
abbrev twoNat : Ty := .tuple (.cons .nat (.cons .nat .nil))
def «N-SP12h» (n : Nat) := run [addHeader 1] ⟨⟨2⟩, [sized .nat (n + 1)], [twoNat], false, none⟩ <|
  .mk [0] [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (item (sized .nat (n + 1))) [0, 10],
    .op ⟨3⟩ [12] (natural n) [],
    .op ⟨4⟩ [13] (item (sized .nat (n + 1))) [0, 12],
    .op ⟨5⟩ [14] (make twoNat) [11, 13],
    .op ⟨6⟩ [15] (get twoNat 0) [14],
    .op ⟨7⟩ [16] (get twoNat 1) [14],
    .op ⟨8⟩ [17] (.call ⟨1⟩) [15, 16],
    .op ⟨9⟩ [18] (make twoNat) [17, 16]] [18]

/-- `N-NL6c` at `total<X = Naturals, n>`: `∑ x ∈ xs, x` on a type member with `add` and `zero`: a
loop that carries the accumulator over `add` from `zero()` (§7.4). -/
def «N-NL6c» (n : Nat) :=
  run [zeroHeader 1, addHeader 2] ⟨⟨3⟩, [sized .nat n], [.nat], false, none⟩ <|
  .mk [0] [
    .op ⟨1⟩ [10] (.call ⟨1⟩) [],
    .loop ⟨2⟩ () (.fixed n) [10] [11]
      (.mk [20, 21] [
        .op ⟨3⟩ [22] (item (sized .nat n)) [0, 20],
        .op ⟨4⟩ [23] (.call ⟨2⟩) [21, 22]] [23])] [11]

/-- `R-NL6c`: `total(xs: [Pair; 4]) -> Pair: ∑ x ∈ xs, x` with the module's `add` and `zero`. -/
abbrev pairRec : Ty := .record ⟨40⟩ false (.cons F (.cons F .nil))
def pairAdd : FnHeader V := ⟨⟨1⟩, [pairRec, pairRec], [pairRec], false, none⟩
def pairZero : FnHeader V := ⟨⟨2⟩, [], [pairRec], false, none⟩
def «R-NL6c» := run [pairAdd, pairZero] ⟨⟨3⟩, [sized pairRec 4], [pairRec], false, none⟩ <|
  .mk [0] [
    .op ⟨1⟩ [10] (.call ⟨2⟩) [],
    .loop ⟨2⟩ () (.fixed 4) [10] [11]
      (.mk [20, 21] [
        .op ⟨3⟩ [22] (item (sized pairRec 4)) [0, 20],
        .op ⟨4⟩ [23] (.call ⟨1⟩) [21, 22]] [23])] [11]

example : «R-FN5a» = .accepted [] := by decide +kernel
example : «N-SP3b» = .accepted [] := by decide +kernel
example : «Naturals-add» = .accepted [] := by decide +kernel
example : («N-SP12h» 0, «N-SP12h» 1, «N-SP12h» 2, «N-SP12h» 3) =
    (.accepted [], .accepted [], .accepted [], .accepted []) := by
  decide +kernel
example : («N-NL6c» 0, «N-NL6c» 1, «N-NL6c» 2, «N-NL6c» 3) =
    (.accepted [], .accepted [], .accepted [], .accepted []) := by
  decide +kernel
example : «R-NL6c» = .accepted [] := by decide +kernel

end Zkc.Vocabulary.Cases.Accepted
