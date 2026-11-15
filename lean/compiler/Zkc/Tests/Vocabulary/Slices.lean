import Zkc.Tests.Vocabulary.Outcome

/-!
Conformance cases of reads and slices, at their instances: a generic definition is written at the
instance that the case names, or at its default instances (SP7: each natural at 0, 1, 2, 3 and at
the upper bound of a `where`), with every static natural a number.
-/

namespace Zkc.Vocabulary.Cases.Slices

open Zkc.Core Zkc.Vocabulary.Cases

/-! ## Slices at an instance -/

/-- `T-Z1` (`take<n = 8, m = 3>`) and `T-Z2` (`bad<n = 8, m = 3>`): `xs[3..8]` into `[F; 5]`. At the
instance the two are one program. -/
def «T-Z1» := check [sized F 8] [sized F 5] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 3) [],
  .op ⟨2⟩ [11] (natural 8) [],
  .op ⟨3⟩ [12] (slice (sized F 8) (sized F 5)) [0, 10, 11]] [12]
def «T-Z2» := «T-Z1»

/-- `T-Z3` at `two<a = 1, b = 2, n = 4>`: `(xs[1..4], ys[2..4])`. -/
abbrev twoSlices : Ty := .tuple (.cons (sized F 3) (.cons (sized F 2) .nil))
def «T-Z3» := check [sized F 4, sized F 4] [twoSlices] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] (natural 4) [],
  .op ⟨3⟩ [12] (slice (sized F 4) (sized F 3)) [0, 10, 11],
  .op ⟨4⟩ [13] (natural 2) [],
  .op ⟨5⟩ [14] (natural 4) [],
  .op ⟨6⟩ [15] (slice (sized F 4) (sized F 2)) [1, 13, 14],
  .op ⟨7⟩ [16] (make twoSlices) [12, 15]] [16]

/-- `half<k = 3>`: `xs[0..2^k]` on `[F; 16]` (`T-Z4`); `use_half<4>` calls it (`T-Z5`). -/
def halfHeader : FnHeader V := ⟨⟨1⟩, [sized F 16], [sized F 8], false, none⟩
def «T-Z4» := run [] halfHeader <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (natural 8) [],
  .op ⟨3⟩ [12] (slice (sized F 16) (sized F 8)) [0, 10, 11]] [12]
def «T-Z5» := run [halfHeader] ⟨⟨2⟩, [sized F 16], [sized F 8], false, none⟩ <|
  .mk [0] [.op ⟨1⟩ [10] (.call ⟨1⟩) [0]] [10]

/-- `T-Z9` at `outer<1, 2, 3, 4>`, which calls `pick<1, 2, 7>`: `xs[a + b + 1]`, the sum written as
applications of `nat.add` to numbers (the frontend may as well write the number 4). -/
def pickHeader : FnHeader V := ⟨⟨1⟩, [sized F 7], [F], false, none⟩
def «T-Z9-pick» := run [] pickHeader <| .mk [0] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] (natural 2) [],
  .op ⟨3⟩ [12] plus [10, 11],
  .op ⟨4⟩ [13] (natural 1) [],
  .op ⟨5⟩ [14] plus [12, 13],
  .op ⟨6⟩ [15] (item (sized F 7)) [0, 14]] [15]
def «T-Z9-outer» := run [pickHeader] ⟨⟨2⟩, [sized F 7], [F], false, none⟩ <|
  .mk [0] [.op ⟨1⟩ [10] (.call ⟨1⟩) [0]] [10]

/-- `R-TY2a` at `fold_all<3>`: the index is static in a slice bound, so the loop is three blocks
of the loop `⟨2⟩` in sequence (§7.4, §7.5); `half` and `2 * half` are numbers. -/
def foldBlock (k size : Nat) : Instruction Raw Unit :=
  .block ⟨2⟩ k [0] (.mk [] [
    .op ⟨3⟩ [20] (natural 0) [],
    .op ⟨4⟩ [21] (natural (size / 2)) [],
    .op ⟨5⟩ [22] (slice (sized F size) (sized F (size / 2))) [0, 20, 21],
    .op ⟨6⟩ [23] (natural (size / 2)) [],
    .op ⟨7⟩ [24] (natural size) [],
    .op ⟨8⟩ [25] (slice (sized F size) (sized F (size / 2))) [0, 23, 24],
    .op ⟨9⟩ [26] (seqAddRow (size / 2)) [22, 25]] [26])
def «R-TY2a» := check [sized F 8] [F] false <| .mk [0] [
  foldBlock 0 8, foldBlock 1 4, foldBlock 2 2,
  .op ⟨10⟩ [11] (natural 0) [],
  .op ⟨11⟩ [12] (item (sized F 1)) [0, 11]] [12]

example : «T-Z1» = .accepted [] := by decide +kernel
example : «T-Z2» = .accepted [] := by decide +kernel
example : «T-Z3» = .accepted [] := by decide +kernel
example : «T-Z4» = .accepted [] := by decide +kernel
example : «T-Z5» = .accepted [] := by decide +kernel
example : «T-Z9-pick» = .accepted [] := by decide +kernel
example : «T-Z9-outer» = .accepted [] := by decide +kernel
example : «R-TY2a» = .accepted [] := by decide +kernel

/-! ## Default instances -/

/-- `R-SP7b` (`first<T, n>`, `T = bool`) and `R-SP7c` (the same with `where (1 <= n)`): `xs[0]`. -/
def first (n : Nat) := check [sized .bool n] [.bool] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (item (sized .bool n)) [0, 10]] [11]

/-- `N-SP7a` (`where (k <= 5)`) and `N-SP7b` (`where (k <= 4)`): `pick<k>(xs: [byte; 5]): xs[k]`. -/
def pickAt (k : Nat) := check [sized byte 5] [byte] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural k) [],
  .op ⟨2⟩ [11] (item (sized byte 5)) [0, 10]] [11]

/-- `N-TY9c` (`if 1 <= n then xs[0] else 0`), `N-TY9d` and `M-FRA17` (`if 0 <= n …`): a static
condition, decided at the instance; the number `0` where a `byte` is expected is a natural
converted by `nat.below`. -/
def firstByte (taken : Bool) (n : Nat) := check [sized byte n] [byte] false <| .mk [0]
  (if taken then [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (item (sized byte n)) [0, 10]]
  else [
    .op ⟨3⟩ [10] (natural 0) [],
    .op ⟨4⟩ [11] (narrowTo 256) [10]]) [11]
def «N-TY9c» (n : Nat) := firstByte (decide (1 ≤ n)) n
def «N-TY9d» (n : Nat) := firstByte (decide (0 ≤ n)) n

/-- `N-TY9f`: `if 2 <= n: pair = xs[0] + xs[1]; acc := pair`. -/
def «N-TY9f» (n : Nat) := check [sized byte n] [.nat] false <| .mk [0]
  (if 2 ≤ n then [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (natural 0) [],
    .op ⟨3⟩ [12] (item (sized byte n)) [0, 11],
    .op ⟨4⟩ [13] (toNat 256) [12],
    .op ⟨5⟩ [14] (natural 1) [],
    .op ⟨6⟩ [15] (item (sized byte n)) [0, 14],
    .op ⟨7⟩ [16] (toNat 256) [15],
    .op ⟨8⟩ [10] plus [13, 16]]
  else [.op ⟨1⟩ [10] (natural 0) []]) [10]

/-- `N-TY2a` (`N = 2^3`) and `N-TY2b` (`N = 2^k`): `xs[N - 1]`, the difference written as
`nat.sub` of numbers (the frontend may as well write the number). -/
def lastAt (size : Nat) := check [sized byte size] [byte] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural size) [],
  .op ⟨2⟩ [11] (natural 1) [],
  .op ⟨3⟩ [12] minus [10, 11],
  .op ⟨4⟩ [13] (item (sized byte size)) [0, 12]] [13]

example : first 0 = .refused [unjustified 2 (item (sized .bool 0)) (.below (.arg 1) 0) [pt 0]] := by
  decide +kernel
example : first 1 = .accepted [] := by decide +kernel
example : first 2 = .accepted [] := by decide +kernel
example : first 3 = .accepted [] := by decide +kernel
example : pickAt 5 = .refused [unjustified 2 (item (sized byte 5)) (.below (.arg 1) 5) [pt 5]] := by
  decide +kernel
example : pickAt 0 = .accepted [] := by decide +kernel
example : pickAt 1 = .accepted [] := by decide +kernel
example : pickAt 2 = .accepted [] := by decide +kernel
example : pickAt 3 = .accepted [] := by decide +kernel
example : pickAt 4 = .accepted [] := by decide +kernel
example : «N-TY9c» 0 = .accepted [] := by decide +kernel
example : «N-TY9c» 1 = .accepted [] := by decide +kernel
example : «N-TY9c» 2 = .accepted [] := by decide +kernel
example : «N-TY9c» 3 = .accepted [] := by decide +kernel
example : «N-TY9d» 0 =
    .refused [unjustified 2 (item (sized byte 0)) (.below (.arg 1) 0) [pt 0]] := by
  decide +kernel
example : «N-TY9f» 0 = .accepted [] := by decide +kernel
example : «N-TY9f» 1 = .accepted [] := by decide +kernel
example : «N-TY9f» 2 = .accepted [] := by decide +kernel
example : «N-TY9f» 3 = .accepted [] := by decide +kernel
example : lastAt 8 = .accepted [] := by decide +kernel
example : lastAt 1 = .accepted [] := by decide +kernel
example : lastAt 2 = .accepted [] := by decide +kernel
example : lastAt 4 = .accepted [] := by decide +kernel

/-! ## Slices of the examples and of the library -/

/-- `M-SUM1` at `sums<v>`: `(sum(table[0..2^v]), sum(table[2^v..2^(v + 2)]))` on `[F; 2^(v + 1)]`;
`sum` of field elements is the row `seq.sum`. -/
abbrev pairF : Ty := .tuple (.cons F (.cons F .nil))
def «M-SUM1» (v : Nat) :=
  let n := 2 ^ (v + 1)
  let h := 2 ^ v
  let e := 2 ^ (v + 2)
  check [sized F n] [pairF] false <| .mk [0] [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (natural h) [],
    .op ⟨3⟩ [12] (slice (sized F n) (sized F h)) [0, 10, 11],
    .op ⟨4⟩ [13] (sumRow (some h)) [12],
    .op ⟨5⟩ [14] (natural h) [],
    .op ⟨6⟩ [15] (natural e) [],
    .op ⟨7⟩ [16] (slice (sized F n) (sized F (e - h))) [0, 14, 15],
    .op ⟨8⟩ [17] (sumRow (some (e - h))) [16],
    .op ⟨9⟩ [18] (make pairF) [13, 17]] [18]

example : «M-SUM1» 0 = .refused [unjustified 7 (slice (sized F 2) (sized F 3))
    (.le (.arg 2) (lengthOf (sized F 2))) [pt 4, pt 2]] := by
  decide +kernel
example : «M-SUM1» 1 = .refused [unjustified 7 (slice (sized F 4) (sized F 6))
    (.le (.arg 2) (lengthOf (sized F 4))) [pt 8, pt 4]] := by
  decide +kernel

/-- `M-FRA6` at `halves<T = bool, n>`: `mut half = (2 * n) / 2`, then
`(xs[0..half], xs[half..2 * half])` where `([T; n], [T; n])` is expected. `half` is a `mut` name, so
no static name (TY2): the bounds are not static, each slice is a `[T]` (TY7), and the conversion
to `[T; n]` is `seq.sized` (TY5, §7.4). `(2 * n) / 2` is written as the number it evaluates to. -/
def «M-FRA6» (n : Nat) (sizedSlices : Bool) :=
  let whole := sized .bool (2 * n)
  let part := sized .bool n
  let sliced := if sizedSlices then part else unsized .bool
  check [whole] [.tuple (.cons part (.cons part .nil))] false <| .mk [0] ([
    .op ⟨1⟩ [10] (natural n) [],
    .op ⟨2⟩ [11] (natural 0) [],
    .op ⟨3⟩ [12] (slice whole sliced) [0, 11, 10],
    .op ⟨4⟩ [13] (natural 2) [],
    .op ⟨5⟩ [14] times [13, 10],
    .op ⟨6⟩ [15] (slice whole sliced) [0, 10, 14]] ++
    (if sizedSlices then [
      .op ⟨9⟩ [18] (make (.tuple (.cons part (.cons part .nil)))) [12, 15]]
    else [
      .op ⟨7⟩ [16] (sizedAs .bool n) [12],
      .op ⟨8⟩ [17] (sizedAs .bool n) [15],
      .op ⟨9⟩ [18] (make (.tuple (.cons part (.cons part .nil)))) [16, 17]])) [18]

example : «M-FRA6» 2 false = .refused [
    unjustified 7 (sizedAs .bool 2) (.exactly (lengthOf (unsized .bool)) 2) [anyNat],
    unjustified 8 (sizedAs .bool 2) (.exactly (lengthOf (unsized .bool)) 2) [anyNat]] := by
  decide +kernel
example : «M-FRA6» 2 true = .accepted [] := by decide +kernel

/-- `L-SEQ3` at `slice<T = bool>`: `values[start..start + count]` without its guard. -/
def «L-SEQ3» := check [unsized .bool, .nat, .nat] [unsized .bool] false <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] plus [1, 2],
  .op ⟨2⟩ [11] (slice (unsized .bool) (unsized .bool)) [0, 1, 10]] [11]

example : «L-SEQ3» = .refused [unjustified 2 (slice (unsized .bool) (unsized .bool))
    (.le (.arg 2) (lengthOf (unsized .bool))) [anyNat, anyNat]] := by
  decide +kernel

/-- `interpolate<F, k>`, as a header. -/
def interpolateHeader (k : Nat) : FnHeader V :=
  ⟨⟨1⟩, [sized F (2 ^ k), cosetTy], [sized F (2 ^ k)], false, none⟩

/-- `L-COS3` at `coefficients<t, k>`: `all_coefficients = interpolate(values, domain)`;
`guard ∀ j ∈ 2^t..2^k, all_coefficients[j] == 0 else refused` (a loop that carries the truth value,
§7.4, its index `2^t` plus the iteration number); `return all_coefficients[0..2^(t + 1)]` into
`[F; 2^t]`. -/
def «L-COS3» (t k : Nat) :=
  let n := 2 ^ k
  let m := 2 ^ t
  run [interpolateHeader k] ⟨⟨2⟩, [sized F n, cosetTy], [sized F m], true, none⟩ <| .mk [0, 1] [
    .op ⟨1⟩ [10] (.call ⟨1⟩) [0, 1],
    .op ⟨2⟩ [11] (truth true) [],
    .loop ⟨3⟩ () (.fixed (n - m)) [11] [12]
      (.mk [20, 21] [
        .op ⟨4⟩ [22] (natural m) [],
        .op ⟨5⟩ [23] plus [22, 20],
        .op ⟨6⟩ [24] (item (sized F n)) [10, 23],
        .op ⟨7⟩ [25] (element 0) [],
        .op ⟨8⟩ [26] (frow .equal) [24, 25],
        .op ⟨9⟩ [27] conj [21, 26]] [27]),
    .guard ⟨10⟩ () 12 .refused,
    .op ⟨11⟩ [13] (natural 0) [],
    .op ⟨12⟩ [14] (natural (2 * m)) [],
    .op ⟨13⟩ [15] (slice (sized F n) (sized F m)) [10, 13, 14]] [15]

example : «L-COS3» 0 0 = .refused [
    unjustified 13 (slice (sized F 1) (sized F 1)) (.le (.arg 2) (lengthOf (sized F 1)))
      [pt 2, pt 1] (fn := 2),
    unjustified 13 (slice (sized F 1) (sized F 1)) (.difference (.arg 2) (.arg 1) 1)
      [pt 2, pt 0] (fn := 2)] := by
  decide +kernel
example : «L-COS3» 0 1 = .refused [
    unjustified 13 (slice (sized F 2) (sized F 1)) (.difference (.arg 2) (.arg 1) 1)
      [pt 2, pt 0] (fn := 2)] := by
  decide +kernel

/-! ## Comprehensions whose body does not run at an instance -/

/-- `L-SEQ1` at `reverse<T = bool, n>`: `[values[n - 1 - i] for i in 0..n]`, a loop that
collects (§7.4); `n - 1` is in its body. -/
def «L-SEQ1» (n : Nat) := check [sized .bool n] [sized .bool n] false <| .mk [0] [
  .loop ⟨1⟩ () (.fixed n) [] [10]
    (.mk [20] [
      .op ⟨2⟩ [21] (natural n) [],
      .op ⟨3⟩ [22] (natural 1) [],
      .op ⟨4⟩ [23] minus [21, 22],
      .op ⟨5⟩ [24] minus [23, 20],
      .op ⟨6⟩ [25] (item (sized .bool n)) [0, 24]] [25])] [10]

/-- `L-SEQ2` at `flatten<T = bool, n, m>` without its `where`:
`[parts[i / m][i % m] for i in 0..n * m]`. -/
def «L-SEQ2» (n m : Nat) :=
  let inner := sized .bool m
  let outer := sized inner n
  check [outer] [sized .bool (n * m)] false <| .mk [0] [
    .loop ⟨1⟩ () (.fixed (n * m)) [] [10]
      (.mk [20] [
        .op ⟨2⟩ [21] (natural m) [],
        .op ⟨3⟩ [22] quotient [20, 21],
        .op ⟨4⟩ [23] (item outer) [0, 22],
        .op ⟨5⟩ [24] remainder [20, 21],
        .op ⟨6⟩ [25] (item inner) [23, 24]] [25])] [10]

/-- `reverse<F, n>`, as a header. -/
def reverseHeader (n : Nat) : FnHeader V := ⟨⟨1⟩, [sized F n], [sized F n], false, none⟩

/-- `L-POLY1` at `divide_linear<F, n>`: the loop collects `carry` at the end of each iteration;
the index is not static in the body, so it is one `local.loop` (§7.4). -/
def «L-POLY1» (n : Nat) :=
  let c := sized F (n + 1)
  let result : Ty := .tuple (.cons (sized F n) (.cons F .nil))
  run [reverseHeader n] ⟨⟨2⟩, [c, F], [result], false, none⟩ <| .mk [0, 1] [
    .op ⟨1⟩ [10] (element 0) [],
    .loop ⟨2⟩ () (.fixed n) [10] [11, 12]
      (.mk [20, 21] [
        .op ⟨3⟩ [22] (natural n) [],
        .op ⟨4⟩ [23] minus [22, 20],
        .op ⟨5⟩ [24] (natural 1) [],
        .op ⟨6⟩ [25] plus [23, 24],
        .op ⟨7⟩ [26] (item c) [0, 25],
        .op ⟨8⟩ [27] (frow .mul) [21, 1],
        .op ⟨9⟩ [28] (frow .add) [26, 27]] [28, 28]),
    .op ⟨10⟩ [13] (.call ⟨1⟩) [12],
    .op ⟨11⟩ [14] (natural 0) [],
    .op ⟨12⟩ [15] (item c) [0, 14],
    .op ⟨13⟩ [16] (frow .mul) [11, 1],
    .op ⟨14⟩ [17] (frow .add) [15, 16],
    .op ⟨15⟩ [18] (make result) [13, 17]] [18]

example : («L-SEQ1» 0, «L-SEQ1» 1, «L-SEQ1» 2, «L-SEQ1» 3) =
    (.accepted [], .accepted [], .accepted [], .accepted []) := by
  decide +kernel
example : ((List.range 4).all fun n => (List.range 4).all fun m =>
    «L-SEQ2» n m == .accepted []) = true := by
  decide +kernel
example : «L-POLY1» 0 = .accepted [] := by decide +kernel
example : «L-POLY1» 1 = .refused
    [unjustified 7 (item (sized F 2)) (.below (.arg 1) 2) [pt 2] (fn := 2)] := by
  decide +kernel
example : «L-POLY1» 2 = .refused
    [unjustified 7 (item (sized F 3)) (.below (.arg 1) 3) [rng 2 3] (fn := 2)] := by
  decide +kernel

end Zkc.Vocabulary.Cases.Slices
