module

public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Data.Nat.Lemmas

@[expose] public section

/-! Total unsigned 64-bit word operations on indices.

The [index contract](../../../../docs/spec/domains/values.md#indices-and-total-word-mathematics)
fixes the all-input meanings of `index.wrapping_add`, `index.wrapping_sub`,
`index.bit_and` and `index.logical_shift_right`. For `M = 2^64`: addition and
subtraction are taken modulo `M`, conjunction is bitwise over the 64 bits, and a
right shift by `b` is `floor(a / 2^b)` for `b < 64` and zero otherwise; the shift
count is not reduced modulo 64. The meanings below read their operands modulo
`M`, so every result is a representable index whatever natural numbers the
operands are. -/

namespace Zkc.Source.Structured

/-- The number of unsigned 64-bit words. -/
def wordModulus : Nat := 2 ^ 64

/-- `(a + b) mod 2^64`. -/
def wrappingAdd (a b : Nat) : Nat := (a + b) % wordModulus

/-- The representative of `a - b` in `[0, 2^64)`. -/
def wrappingSubtract (a b : Nat) : Nat := (a % wordModulus + (wordModulus - b % wordModulus)) % wordModulus

/-- Bitwise conjunction of the two 64-bit words. -/
def bitAnd (a b : Nat) : Nat := (a % wordModulus) &&& (b % wordModulus)

/-- `floor(a / 2^b)` for a shift count below 64, and zero otherwise. -/
def logicalShiftRight (a b : Nat) : Nat := if b < 64 then (a % wordModulus) >>> b else 0

theorem wordModulus_pos : 0 < wordModulus := Nat.two_pow_pos 64

theorem wrappingAdd_lt (a b : Nat) : wrappingAdd a b < wordModulus :=
  Nat.mod_lt _ wordModulus_pos

theorem wrappingSubtract_lt (a b : Nat) : wrappingSubtract a b < wordModulus :=
  Nat.mod_lt _ wordModulus_pos

/-- Subtraction undoes addition on the words. -/
theorem wrappingAdd_wrappingSubtract (a b : Nat) :
    wrappingAdd (wrappingSubtract a b) b = a % wordModulus := by
  have hb := Nat.mod_lt b wordModulus_pos
  unfold wrappingAdd wrappingSubtract
  rw [Nat.add_mod _ b, Nat.mod_mod, Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hb),
    Nat.add_mod_right, Nat.mod_mod]

/-- On representable operands subtraction without borrow is natural subtraction. -/
theorem wrappingSubtract_of_le {a b : Nat} (below : a < wordModulus) (le : b ≤ a) :
    wrappingSubtract a b = a - b := by
  have hb : b < wordModulus := Nat.lt_of_le_of_lt le below
  unfold wrappingSubtract
  rw [Nat.mod_eq_of_lt below, Nat.mod_eq_of_lt hb]
  have : a + (wordModulus - b) = (a - b) + wordModulus := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem bitAnd_lt (a b : Nat) : bitAnd a b < wordModulus :=
  Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ wordModulus_pos)

theorem logicalShiftRight_lt (a b : Nat) : logicalShiftRight a b < wordModulus := by
  unfold logicalShiftRight
  split
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ wordModulus_pos)
  · exact wordModulus_pos

/-- A shift by a count below 64 divides by its power of two. -/
theorem logicalShiftRight_of_lt (a : Nat) {b : Nat} (below : b < 64) :
    logicalShiftRight a b = a % wordModulus / 2 ^ b := by
  simp [logicalShiftRight, below, Nat.shiftRight_eq_div_pow]

/-- A shift count of at least 64 is not reduced: the result is zero. -/
theorem logicalShiftRight_of_le (a : Nat) {b : Nat} (le : 64 ≤ b) : logicalShiftRight a b = 0 := by
  simp [logicalShiftRight, Nat.not_lt.mpr le]

end Zkc.Source.Structured
