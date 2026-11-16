import Zkc.Tests.Vocabulary.Outcome

/-!
Conformance cases of loops, comprehensions, collected values, linear records and empty types.
-/

namespace Zkc.Vocabulary.Cases.Loops

open Zkc.Core Zkc.Vocabulary.Cases

/-- The tuple `([byte; 2], [byte; 4], [byte; 8])`. -/
abbrev triple : Ty :=
  .tuple (.cons (sized byte 2) (.cons (sized byte 4) (.cons (sized byte 8) .nil)))

/-- `N-TY10a`: `for j in 0..3: x = t[j]; acc := acc + x[0]`. The index is a tuple position, so the
loop is typed per iteration and is three blocks of the loop `⟨2⟩` (§7.4, §7.5). Each value of
`acc` has its own name: block `j` reads `10 + j` and binds `11 + j`, and the names inside it are
`20 + 10 * j` and after. -/
def firstsBlock (j size : Nat) : Instruction Raw Unit :=
  let base := 20 + 10 * j
  .block ⟨2⟩ j [11 + j] (.mk [] [
    .op ⟨3⟩ [base] (get triple j) [0],
    .op ⟨4⟩ [base + 1] (natural 0) [],
    .op ⟨5⟩ [base + 2] (item (sized byte size)) [base, base + 1],
    .op ⟨6⟩ [base + 3] (toNat 256) [base + 2],
    .op ⟨7⟩ [base + 4] plus [10 + j, base + 3]] [base + 4])
def «N-TY10a» := check [triple] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  firstsBlock 0 2, firstsBlock 1 4, firstsBlock 2 8] [13]

/-- `N-TY11a`: `[t[j][0] for j in 0..3]`, typed per element: a `local.make` of its elements. -/
def «N-TY11a» := check [triple] [sized byte 3] false <| .mk [0] [
  .op ⟨1⟩ [10] (get triple 0) [0],
  .op ⟨2⟩ [11] (natural 0) [],
  .op ⟨3⟩ [12] (item (sized byte 2)) [10, 11],
  .op ⟨4⟩ [13] (get triple 1) [0],
  .op ⟨5⟩ [14] (item (sized byte 4)) [13, 11],
  .op ⟨6⟩ [15] (get triple 2) [0],
  .op ⟨7⟩ [16] (item (sized byte 8)) [15, 11],
  .op ⟨8⟩ [17] (make (sized byte 3)) [12, 14, 16]] [17]

/-- The tuple of the collected `parts` of `N-TY16b`. -/
abbrev partsTy : Ty :=
  .tuple (.cons (sized byte 0)
    (.cons (sized byte 1) (.cons (sized byte 2) (.cons (sized byte 3) .nil))))

/-- `N-TY16b`: `for i in 0..4 collect (parts = xs[0..i]): ()`, then `length(parts[3])`: four
blocks, and the tuple of their values (§7.4). The names inside block `i` are `40 + 10 * i` and
after. -/
def partBlock (i : Nat) : Instruction Raw Unit :=
  let base := 40 + 10 * i
  .block ⟨1⟩ i [30 + i] (.mk [] [
    .op ⟨2⟩ [base] (natural 0) [],
    .op ⟨3⟩ [base + 1] (natural i) [],
    .op ⟨4⟩ [base + 2] (slice (sized byte 4) (sized byte i)) [0, base, base + 1]] [base + 2])
def «N-TY16b» := check [sized byte 4] [.nat] false <| .mk [0] [
  partBlock 0, partBlock 1, partBlock 2, partBlock 3,
  .op ⟨5⟩ [10] (make partsTy) [30, 31, 32, 33],
  .op ⟨6⟩ [11] (get partsTy 3) [10],
  .op ⟨7⟩ [12] (length (sized byte 3)) [11]] [12]

/-- `N-TY10d`: `rest := low(rest)` three times, stepped: the instances `low<byte, 2>`,
`low<byte, 1>` and `low<byte, 0>` (keys 1, 2, 3), then `shrink` (key 4). Each value of `rest`
has its own name: block `j` reads `j` and binds `j + 1`. -/
def lowHeader (key m : Nat) : FnHeader V :=
  ⟨⟨key⟩, [sized byte (2 ^ (m + 1))], [sized byte (2 ^ m)], false, none⟩
def lowBody (m : Nat) : Region Raw Unit := .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (natural (2 ^ m)) [],
  .op ⟨3⟩ [12] (slice (sized byte (2 ^ (m + 1))) (sized byte (2 ^ m))) [0, 10, 11]] [12]
def «N-TY10d-low» := (run [] (lowHeader 1 2) (lowBody 2),
  run [lowHeader 1 2] (lowHeader 2 1) (lowBody 1),
  run [lowHeader 1 2, lowHeader 2 1] (lowHeader 3 0) (lowBody 0))
def «N-TY10d» := run [lowHeader 1 2, lowHeader 2 1, lowHeader 3 0]
    ⟨⟨4⟩, [sized byte 8], [byte], false, none⟩ <| .mk [0] [
  .block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [20] (.call ⟨1⟩) [0]] [20]),
  .block ⟨1⟩ 1 [2] (.mk [] [.op ⟨2⟩ [30] (.call ⟨2⟩) [1]] [30]),
  .block ⟨1⟩ 2 [3] (.mk [] [.op ⟨2⟩ [40] (.call ⟨3⟩) [2]] [40]),
  .op ⟨3⟩ [10] (natural 0) [],
  .op ⟨4⟩ [11] (item (sized byte 1)) [3, 10]] [11]

/-- `N-TY10f`: `mut acc = 0; for i in 0..4: acc := acc + xs[i]`. -/
def «N-TY10f» := check [sized byte 4] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 4) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (item (sized byte 4)) [0, 20],
      .op ⟨4⟩ [23] (toNat 256) [22],
      .op ⟨5⟩ [24] plus [21, 23]] [24])] [11]

/-- `N-CT4a`: `for i in 0..n: acc := acc + i` with `n: nat`: the count is `n - 0` and the index
`0` plus the iteration number, as the test `I-4e-total` writes a run-time range. -/
def «N-CT4a» := check [.nat] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (natural 0) [],
  .op ⟨3⟩ [12] minus [0, 11],
  .loop ⟨4⟩ () (.count 12) [10] [13]
    (.mk [20, 21] [
      .op ⟨5⟩ [22] plus [11, 20],
      .op ⟨6⟩ [23] plus [21, 22]] [23])] [13]

/-- `X-FN7a`: `for x in xs: total := total + x` with `xs: [byte]`: as often as the length, the
element read at the iteration number; and `square(x) = x * x`. -/
def «X-FN7a» := check [unsized byte] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length (unsized byte)) [0],
  .loop ⟨3⟩ () (.count 11) [10] [12]
    (.mk [20, 21] [
      .op ⟨4⟩ [22] (item (unsized byte)) [0, 20],
      .op ⟨5⟩ [23] (toNat 256) [22],
      .op ⟨6⟩ [24] plus [21, 23]] [24])] [12]
def «X-FN7a-square» := check [.nat] [.nat] false <| .mk [0] [.op ⟨1⟩ [10] times [0, 0]] [10]

/-- `T-Z14b`: `∑ x ∈ values, x` on field elements: a loop as often as the length that collects
the element, then `seq.sum` (§7.4). -/
def «T-Z14b» := check [unsized F] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (length (unsized F)) [0],
  .loop ⟨2⟩ () (.count 10) [] [11]
    (.mk [20] [.op ⟨3⟩ [21] (item (unsized F)) [0, 20]] [21]),
  .op ⟨4⟩ [12] (sumRow none) [11]] [12]

/-! ## `R-LIB1`: the library functions at the instances that it reaches -/

/-- `count<8>`: `∑ f ∈ flags, if f then 1 else 0` into `index<9>`: a loop that carries the
natural accumulator (§7.4), then `nat.below`. -/
def «R-LIB1-count» := check [sized .bool 8] [.fin 9] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 8) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (item (sized .bool 8)) [0, 20],
      .choose ⟨4⟩ () 22 [23]
        (.mk [] [.op ⟨5⟩ [30] (natural 1) []] [30])
        (.mk [] [.op ⟨6⟩ [40] (natural 0) []] [40]),
      .op ⟨7⟩ [24] plus [21, 23]] [24]),
  .op ⟨8⟩ [12] (narrowTo 9) [11]] [12]

/-- `enumerate<G1, 4>`: `[(i, values[i]) for i in 0..4]`; the index where `index<4>` is
expected is converted by `nat.below`. -/
abbrev numbered : Ty := .tuple (.cons (.fin 4) (.cons G1 .nil))
def «R-LIB1-enumerate» := check [sized G1 4] [sized numbered 4] false <| .mk [0] [
  .loop ⟨1⟩ () (.fixed 4) [] [10]
    (.mk [20] [
      .op ⟨2⟩ [21] (narrowTo 4) [20],
      .op ⟨3⟩ [22] (item (sized G1 4)) [0, 20],
      .op ⟨4⟩ [23] (make numbered) [21, 22]] [23])] [10]

/-- `zip<G1, Fr, 4>`: `[(left[i], right[i]) for i in 0..4]`. -/
abbrev zipped : Ty := .tuple (.cons G1 (.cons Fr .nil))
def «R-LIB1-zip» := check [sized G1 4, sized Fr 4] [sized zipped 4] false <| .mk [0, 1] [
  .loop ⟨1⟩ () (.fixed 4) [] [10]
    (.mk [20] [
      .op ⟨2⟩ [21] (item (sized G1 4)) [0, 20],
      .op ⟨3⟩ [22] (item (sized Fr 4)) [1, 20],
      .op ⟨4⟩ [23] (make zipped) [21, 22]] [23])] [10]

/-- `low<G1, 2>` and `high<G1, 2>`, which `fold<G1, 2>` calls. -/
def «R-LIB1-low» := check [sized G1 8] [sized G1 4] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (natural 4) [],
  .op ⟨3⟩ [12] (slice (sized G1 8) (sized G1 4)) [0, 10, 11]] [12]
def «R-LIB1-high» := check [sized G1 8] [sized G1 4] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 4) [],
  .op ⟨2⟩ [11] (natural 8) [],
  .op ⟨3⟩ [12] (slice (sized G1 8) (sized G1 4)) [0, 10, 11]] [12]

/-! ## Empty types and a linear record -/

/-- `X-TY1a`: `impossible(x: index<0>) -> index<0>: x`; `empty() -> [index<0>; 0]: []`. -/
def «X-TY1a-impossible» := check [.fin 0] [.fin 0] false <| .mk [0] [] [0]
def «X-TY1a-empty» := check [] [sized (.fin 0) 0] false <| .mk [] [
  .op ⟨1⟩ [10] (make (sized (.fin 0) 0)) []] [10]

/-- The linear record `Ticket<F>`: `point: [F]`, `value: F`. -/
abbrev ticketTy : Ty := .record ⟨70⟩ true (.cons (unsized F) (.cons F .nil))

/-- `M-FRA3`: `Ticket{point, value} = ticket; return value`, a `local.take` of the whole record;
`point` is not linear, so leaving it unused is no misuse. The original `Ticket{point = _, value}`
is the same core program. -/
def «M-FRA3» := check [ticketTy] [F] false <| .mk [0] [
  .op ⟨1⟩ [10, 11] (take ticketTy) [0]] [11]

example : «N-TY10a» = .accepted [] := by decide +kernel
example : «N-TY11a» = .accepted [] := by decide +kernel
example : «N-TY16b» = .accepted [] := by decide +kernel
example : «N-TY10d-low» = (.accepted [], .accepted [], .accepted []) := by decide +kernel
example : «N-TY10d» = .accepted [] := by decide +kernel
example : «N-TY10f» = .accepted [] := by decide +kernel
example : «N-CT4a» = .accepted [] := by decide +kernel
example : «X-FN7a» = .accepted [] := by decide +kernel
example : «X-FN7a-square» = .accepted [] := by decide +kernel
example : «T-Z14b» = .accepted [] := by decide +kernel
example : «R-LIB1-count» = .accepted [] := by decide +kernel
example : «R-LIB1-enumerate» = .accepted [] := by decide +kernel
example : «R-LIB1-zip» = .accepted [] := by decide +kernel
example : «R-LIB1-low» = .accepted [] := by decide +kernel
example : «R-LIB1-high» = .accepted [] := by decide +kernel
example : «X-TY1a-impossible» = .accepted [] := by decide +kernel
example : «X-TY1a-empty» = .accepted [] := by decide +kernel
example : «M-FRA3» = .accepted [] := by decide +kernel
end Zkc.Vocabulary.Cases.Loops
