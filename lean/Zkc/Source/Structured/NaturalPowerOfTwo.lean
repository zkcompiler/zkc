module

public import Init.Data.Nat.Power2.Bitwise
public import Init.Data.Nat.Lemmas
import all Init.Data.Nat.Power2.Basic

@[expose] public section

namespace Zkc.Source.Structured

/-- Decide `n = 2^r` using only the bits and logarithm of `n`. In particular,
the work never constructs a power whose size depends on the supplied exponent.
Lean's `Nat.isPowerOfTwo` decision procedure checks `n ≠ 0` and
`n &&& (n - 1) = 0`. There is no machine-index cutoff. -/
def naturalPowerOfTwo (n r : Nat) : Bool :=
  decide n.isPowerOfTwo && decide (n.log2 = r)

theorem naturalPowerOfTwo_eq_true (n r : Nat) :
    naturalPowerOfTwo n r = true ↔ n = 2 ^ r := by
  simp only [naturalPowerOfTwo, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hn, hr⟩
    obtain ⟨k, hk⟩ := hn
    rw [hk, Nat.log2_two_pow] at hr
    exact hr ▸ hk
  · intro h
    exact ⟨⟨r, h⟩, by rw [h, Nat.log2_two_pow]⟩

theorem naturalPowerOfTwo_eq_decide (n r : Nat) :
    naturalPowerOfTwo n r = decide (n = 2 ^ r) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using naturalPowerOfTwo_eq_true n r

/-- A guarded natural shift agrees on representable inputs. This is an
arithmetic law, not a theorem about native execution or machine shifts. -/
theorem guarded_shift_powerOfTwo (n r : Nat) (representable : n < 2 ^ 64) :
    (if r < 64 then n = (1 <<< r) else False) ↔ n = 2 ^ r := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  constructor
  · split <;> simp_all
  · intro h
    have bound : r < 64 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (h ▸ representable)
    simp only [bound, ↓reduceIte, h]

end Zkc.Source.Structured
