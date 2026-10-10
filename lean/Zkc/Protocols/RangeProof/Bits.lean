import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Bounded integer interpretation of bit witnesses

Bits are least significant first within each value. This connects an actual
Boolean witness and its field reconstruction to a bounded canonical integer;
it does not extract bits from a cryptographic proof.
-/

set_option autoImplicit false

namespace Zkc.Protocols.RangeProof

/-- Little-endian binary reconstruction using Mathlib's numeral interpretation. -/
def ofBits (bits : List Bool) : Nat :=
  Nat.ofDigits 2 (bits.map Bool.toNat)

theorem ofBits_lt (bits : List Bool) : ofBits bits < 2 ^ bits.length := by
  have digits : ∀ x ∈ bits.map Bool.toNat, x < 2 := by
    intro x hx
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hx
    cases bit <;> decide
  simpa only [ofBits, List.length_map] using
    Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) digits

/-- No primality assumption is needed for injectivity below the modulus. -/
theorem reconstruction_range {p : Nat} (value : ZMod p) (bits : List Bool)
    (fits : 2 ^ bits.length ≤ p) (reconstructs : value = (ofBits bits : ZMod p)) :
    value.val < 2 ^ bits.length := by
  rw [reconstructs, ZMod.val_natCast_of_lt (lt_of_lt_of_le (ofBits_lt bits) fits)]
  exact ofBits_lt bits

end Zkc.Protocols.RangeProof
