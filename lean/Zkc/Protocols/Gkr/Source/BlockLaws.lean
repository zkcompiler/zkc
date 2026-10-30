module

public import Zkc.Polynomial.Multilinear.ListRestriction
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! Source-independent row-major block selection laws. -/
namespace ZkcExamples.Structured.GkrSourceLaws
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The block of `size` values at `position`. -/
def block (xs : List F) (position size : Nat) : List F := (xs.drop (position * size)).take size

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem block_length (xs : List F) (position size : Nat) (inside : (position + 1) * size ≤ xs.length) :
    (block xs position size).length = size := by
  simp only [block, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at inside
  omega

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The two halves of a block of even size are the blocks of half the size. -/
theorem block_halves (xs : List F) (position half : Nat) :
    (block xs position (2 * half)).take half = block xs (2 * position) half ∧
      (block xs position (2 * half)).drop half = block xs (2 * position + 1) half := by
  constructor
  · simp only [block, List.take_take]
    rw [Nat.min_eq_left (by omega : half ≤ 2 * half)]
    congr 2
    ring
  · simp only [block, List.drop_take, List.drop_drop]
    rw [show 2 * half - half = half by omega]
    congr 2
    ring

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem block_whole (xs : List F) (size : Nat) (whole : xs.length = size) : block xs 0 size = xs := by
  simp [block, ← whole]

/-- The position's leading bits above `r - 1`: twice those above `r`, plus the
bit at `r - 1`. -/
theorem position_split (position r : Nat) (positive : 1 ≤ r) :
    position / 2 ^ (r - 1) = 2 * (position / 2 ^ r) + position / 2 ^ (r - 1) % 2 := by
  have above : position / 2 ^ r = position / 2 ^ (r - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel positive]
  rw [above]
  exact (Nat.div_add_mod _ 2).symm

omit [CommRing F] [DecidableEq F] in
/-- One iteration of the selection: the block at the leading bits above
`r - 1`, from the block at the leading bits above `r`. -/
theorem block_step (xs : List F) (position size r : Nat) (positive : 1 ≤ r) :
    (if position / 2 ^ (r - 1) % 2 = 1 then
        (block xs (position / 2 ^ r) (size * 2 ^ r)).drop (size * 2 ^ (r - 1))
      else (block xs (position / 2 ^ r) (size * 2 ^ r)).take (size * 2 ^ (r - 1))) =
      block xs (position / 2 ^ (r - 1)) (size * 2 ^ (r - 1)) := by
  have doubled : size * 2 ^ r = 2 * (size * 2 ^ (r - 1)) := by
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  rw [doubled]
  obtain ⟨low, high⟩ := block_halves xs (position / 2 ^ r) (size * 2 ^ (r - 1))
  have split := position_split position r positive
  split
  · rename_i bit
    rw [high, split, bit]
  · rename_i bit
    have zero : position / 2 ^ (r - 1) % 2 = 0 := by omega
    rw [low, split, zero, Nat.add_zero]

end ZkcExamples.Structured.GkrSourceLaws
