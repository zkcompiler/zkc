import Zkc.Tests.Vocabulary.Outcome

/-!
Conformance cases of the ranges of arithmetic, of conditions, of `and` and of `nonzero`, written
by names as a frontend would give them, at koala-bear in place of bls12-381.fr (no verdict here
depends on the field). Each `example` pins the outcome.
-/

namespace Zkc.Vocabulary.Cases.Ranges

open Zkc.Core Zkc.Vocabulary.Cases

/-! ## The power -/

/-- `V-F5`: `def f(x: index<6>, y: index<4>, z: nat) -> nat: z / (x ^ y)`. -/
def «V-F5» := check [.fin 6, .fin 4, .nat] [.nat] false <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 6) [0],
  .op ⟨2⟩ [11] (toNat 4) [1],
  .op ⟨3⟩ [12] power [10, 11],
  .op ⟨4⟩ [13] quotient [2, 12]] [13]

/-- `V-F5b`: `def f(x: index<6>, y: index<4>) -> nat: x ^ y - 1`. -/
def «V-F5b» := check [.fin 6, .fin 4] [.nat] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (toNat 6) [0],
  .op ⟨2⟩ [11] (toNat 4) [1],
  .op ⟨3⟩ [12] power [10, 11],
  .op ⟨4⟩ [13] (natural 1) [],
  .op ⟨5⟩ [14] minus [12, 13]] [14]

/-- `V-F5c`: `def f(xs: [F; 1], x: index<1>, y: index<4>) -> F: xs[x ^ y]`. -/
def «V-F5c» := check [sized F 1, .fin 1, .fin 4] [F] false <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 1) [1],
  .op ⟨2⟩ [11] (toNat 4) [2],
  .op ⟨3⟩ [12] power [10, 11],
  .op ⟨4⟩ [13] (item (sized F 1)) [0, 12]] [13]

/-- `N-TY8a`: `guard 1 <= x else refused; return z / (x ^ y)`; `1 <= x` is
`bool.not(nat.less(x, 1))` (§7.4). -/
def «N-TY8a» := check [.fin 6, .fin 4, .nat] [.nat] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 6) [0],
  .op ⟨2⟩ [11] (natural 1) [],
  .op ⟨3⟩ [12] less [10, 11],
  .op ⟨4⟩ [13] negation [12],
  .guard ⟨5⟩ () 13 .refused,
  .op ⟨6⟩ [14] (toNat 6) [0],
  .op ⟨7⟩ [15] (toNat 4) [1],
  .op ⟨8⟩ [16] power [14, 15],
  .op ⟨9⟩ [17] quotient [2, 16]] [17]

/-- `N-TY8b`: `def f(x: index<6>, z: nat) -> nat: z / (x ^ 0)`. -/
def «N-TY8b» := check [.fin 6, .nat] [.nat] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (toNat 6) [0],
  .op ⟨2⟩ [11] (natural 0) [],
  .op ⟨3⟩ [12] power [10, 11],
  .op ⟨4⟩ [13] quotient [1, 12]] [13]

/-- `N-TY8c`: `def f(xs: [F; 2], x: index<1>, y: index<4>) -> F: xs[x ^ y]`. -/
def «N-TY8c» := check [sized F 2, .fin 1, .fin 4] [F] false <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 1) [1],
  .op ⟨2⟩ [11] (toNat 4) [2],
  .op ⟨3⟩ [12] power [10, 11],
  .op ⟨4⟩ [13] (item (sized F 2)) [0, 12]] [13]

example : «V-F5» = .refused [unjustified 4 quotient (.atLeast (.arg 1) 1) [rng 0 125]] := by
  decide +kernel
example : «V-F5b» = .refused [unjustified 5 minus (.le (.arg 1) (.arg 0)) [pt 1, rng 0 125]] := by
  decide +kernel
example : «V-F5c» = .refused [unjustified 4 (item (sized F 1)) (.below (.arg 1) 1) [rng 0 1]] := by
  decide +kernel
example : «N-TY8a» = .accepted [] := by decide +kernel
example : «N-TY8b» = .accepted [] := by decide +kernel
example : «N-TY8c» = .accepted [] := by decide +kernel

/-! ## Choices, `and`, literals of naturals -/

/-- `N-TY6e`: `def f(c: bool) -> index<2>: if c then 1 else 0`. The numbers are naturals (TY6), the
`if` a natural of the hull of its arms (TY8), converted by `nat.below` where `index<2>` is
expected (TY5). -/
def «N-TY6e» := check [.bool] [.fin 2] false <| .mk [0] [
  .choose ⟨1⟩ () 0 [10]
    (.mk [] [.op ⟨2⟩ [20] (natural 1) []] [20])
    (.mk [] [.op ⟨3⟩ [30] (natural 0) []] [30]),
  .op ⟨4⟩ [11] (narrowTo 2) [10]] [11]

/-- `N-TY6b`: `y = if 0 < length(xs) then xs[0] else 0; return y`. -/
def «N-TY6b» := check [unsized F] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length (unsized F)) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [.op ⟨5⟩ [20] (natural 0) [], .op ⟨6⟩ [21] (item (unsized F)) [0, 20]] [21])
    (.mk [] [.op ⟨7⟩ [30] (element 0) []] [30])] [13]

/-- `N-TY6c`: `∑ i ∈ 0..4, if ws[i] == z then values[i] else 0` on field elements: a loop that
collects the term, then the row `seq.sum` (§7.4). -/
def «N-TY6c» := check [sized F 4, sized F 4, F] [F] false <| .mk [0, 1, 2] [
  .loop ⟨1⟩ () (.fixed 4) [] [10]
    (.mk [20] [
      .op ⟨2⟩ [21] (item (sized F 4)) [0, 20],
      .op ⟨3⟩ [22] (frow .equal) [21, 2],
      .choose ⟨4⟩ () 22 [23]
        (.mk [] [.op ⟨5⟩ [30] (item (sized F 4)) [1, 20]] [30])
        (.mk [] [.op ⟨6⟩ [40] (element 0) []] [40])] [23]),
  .op ⟨7⟩ [11] (sumRow (some 4)) [10]] [11]

/-- `V-F9`: `if not (i < length(xs)): out := xs[i]`. -/
def «V-F9» := check [unsized F, .nat] [F] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (element 0) [],
  .op ⟨2⟩ [11] (length (unsized F)) [0],
  .op ⟨3⟩ [12] less [1, 11],
  .op ⟨4⟩ [13] negation [12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [.op ⟨6⟩ [20] (item (unsized F)) [0, 1]] [20])
    (.mk [] [] [10])] [14]

/-- `M-FRA18`: `ratio` of `examples/fragments.zkc` without `guard 1 <= x - y`. -/
def «M-FRA18» := check [.fin 10, .fin 5, .fin 5] [.nat] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 5) [2],
  .op ⟨2⟩ [11] (toNat 5) [1],
  .op ⟨3⟩ [12] less [11, 10],
  .op ⟨4⟩ [13] negation [12],
  .guard ⟨5⟩ () 13 .refused,
  .op ⟨6⟩ [14] (toNat 10) [0],
  .op ⟨7⟩ [15] (toNat 5) [1],
  .op ⟨8⟩ [16] (toNat 5) [2],
  .op ⟨9⟩ [17] minus [15, 16],
  .op ⟨10⟩ [18] quotient [14, 17]] [18]

/-- `M-FRA4`: `first` of `examples/fragments.zkc` without its guard: the body cannot stop, so the
header says so (FN2). -/
def «M-FRA4» := check [unsized F] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (item (unsized F)) [0, 10]] [11]

/-- `Option<F>`: `Some` at position 0, `None` (the empty tuple) at position 1. -/
abbrev opt : Ty := .variant ⟨7⟩ (.cons F (.cons (.tuple .nil) .nil))

/-- `M-FRA5`: `if 0 < length(xs) then None else Some(xs[0])`. -/
def «M-FRA5» := check [unsized F] [opt] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length (unsized F)) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [
      .op ⟨5⟩ [20] (make (.tuple .nil)) [],
      .op ⟨6⟩ [21] (variant opt 1) [20]] [21])
    (.mk [] [
      .op ⟨7⟩ [30] (natural 0) [],
      .op ⟨8⟩ [31] (item (unsized F)) [0, 30],
      .op ⟨9⟩ [32] (variant opt 0) [31]] [32])] [13]

/-- `M-FRA15` (and `N-TY9a`, the same function): `xs[0] == 0 and 0 < length(xs)`. The right
operand cannot stop and applies no operation with a domain, so `and` is `bool.and` (§7.4). -/
def «M-FRA15» := check [unsized F] [.bool] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (item (unsized F)) [0, 10],
  .op ⟨3⟩ [12] (element 0) [],
  .op ⟨4⟩ [13] (frow .equal) [11, 12],
  .op ⟨5⟩ [14] (natural 0) [],
  .op ⟨6⟩ [15] (length (unsized F)) [0],
  .op ⟨7⟩ [16] less [14, 15],
  .op ⟨8⟩ [17] conj [13, 16]] [17]

example : «N-TY6e» = .accepted [] := by decide +kernel
example : «N-TY6b» = .accepted [] := by decide +kernel
example : «N-TY6c» = .accepted [] := by decide +kernel
example : «V-F9» = .refused
    [unjustified 6 (item (unsized F)) (.lt (.arg 1) (lengthOf (unsized F))) [anyNat, anyNat]] := by
  decide +kernel
example : «M-FRA18» = .refused [unjustified 10 quotient (.atLeast (.arg 1) 1) [rng 0 4]] := by
  decide +kernel
example : «M-FRA4» = .refused
    [unjustified 2 (item (unsized F)) (.lt (.arg 1) (lengthOf (unsized F))) [pt 0, anyNat]] := by
  decide +kernel
example : «M-FRA5» = .refused
    [unjustified 8 (item (unsized F)) (.lt (.arg 1) (lengthOf (unsized F))) [pt 0, rng 0 0]] := by
  decide +kernel
example : «M-FRA15» = .refused
    [unjustified 2 (item (unsized F)) (.lt (.arg 1) (lengthOf (unsized F))) [pt 0, anyNat]] := by
  decide +kernel
end Zkc.Vocabulary.Cases.Ranges
