import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-! Recover natural-number equality from a field equation only when both
expressions are bounded below its characteristic. These lemmas isolate the
integer-adequacy obligation of machine arithmetic and transaction balance.
They do not extract witnesses from commitments or prove a protocol secure. -/

set_option autoImplicit false

namespace Zkc.Algebra

theorem bounded_residue_eq {p a b : Nat} [NeZero p]
    (ha : a < p) (hb : b < p) (equal : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have values := congrArg ZMod.val equal
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using values

/-- A checked modular balance implies integer balance after the shared-opening
and field-conservation premises have been established separately. Bounds on
individual amounts alone do not imply the required bounds on their totals. -/
theorem integer_conservation {p incoming outgoing fee : Nat} [NeZero p]
    (hin : incoming < p) (hout : outgoing + fee < p)
    (balanced : (incoming : ZMod p) = (outgoing : ZMod p) + (fee : ZMod p)) :
    incoming = outgoing + fee := by
  apply bounded_residue_eq hin hout
  simpa only [Nat.cast_add] using balanced

/-- The same no-wrap boundary validates a word-addition constraint. The carry
is a bit, both input words and the result are bounded, and the field is large
enough for the *whole expressions*, not just each individual word. -/
theorem word_addition {p base a b result carry : Nat} [NeZero p]
    (ha : a < base) (hb : b < base)
    (hr : result < base) (hc : carry = 0 ∨ carry = 1)
    (hp : 2 * base ≤ p)
    (equation : (a : ZMod p) + (b : ZMod p) =
      (result : ZMod p) + (base : ZMod p) * (carry : ZMod p)) :
    result = (a + b) % base := by
  have left : a + b < p := by omega
  have right : result + base * carry < p := by rcases hc with h | h <;> simp [h] <;> omega
  have exact : a + b = result + base * carry := bounded_residue_eq left right (by
    simpa only [Nat.cast_add, Nat.cast_mul] using equation)
  rw [exact, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

end Zkc.Algebra
