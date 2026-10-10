import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

/-!
# UniformIndex by reducing a uniform word

The native UniformIndex(N) sampler reads one `w`-bit word and returns its
residue modulo `N` (docs/spec/runtime/services.md#uniformindex-realization).
This module proves the counting fact behind its exactness claim: over all
`w`-bit words, every residue below `N` has the same number of preimages exactly
when `N` is a power of two no larger than `2^w`.

These are statements about the arithmetic map on words. They do not model the
native transcript, its framing, the origin or bound absorption, or whether
provider bytes are uniform; no native correspondence is claimed.
-/

namespace Zkc.Probability.UniformIndex

/-- The words below `2^w` whose residue modulo `N` is `i`. -/
def fiber (w N i : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ w)).filter (fun x => x % N = i)

/-- For `N = 2^k` with `k ≤ w`, each residue has exactly `2^(w-k)` preimages. -/
theorem fiber_card_pow {w k i : ℕ} (hk : k ≤ w) (hi : i < 2 ^ k) :
    (fiber w (2 ^ k) i).card = 2 ^ (w - k) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hw : 2 ^ w = 2 ^ (w - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have image : fiber w (2 ^ k) i =
      (Finset.range (2 ^ (w - k))).image (fun q => q * 2 ^ k + i) := by
    ext x
    simp only [fiber, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, rfl⟩
      refine ⟨x / 2 ^ k, ?_, Nat.div_add_mod' x (2 ^ k)⟩
      rw [hw] at hx
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hx)
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hw]
        calc q * 2 ^ k + i < (q + 1) * 2 ^ k := by rw [add_mul, one_mul]; omega
          _ ≤ 2 ^ (w - k) * 2 ^ k := Nat.mul_le_mul_right _ hq
      · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  rw [image, Finset.card_image_of_injective _ (fun a b h => by
    simpa [Nat.mul_left_inj hpos.ne'] using h), Finset.card_range]

/-- The fibers below `N` partition the words, so equal fibers force `N ∣ 2^w`. -/
theorem dvd_of_equal_fibers {w N c : ℕ} (hN : 0 < N)
    (equal : ∀ i < N, (fiber w N i).card = c) : N ∣ 2 ^ w := by
  have partition : (Finset.range (2 ^ w)).card =
      ∑ i ∈ Finset.range N, (fiber w N i).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.2 (Nat.mod_lt x hN))
  rw [Finset.card_range,
    Finset.sum_const_nat (fun i hi => equal i (Finset.mem_range.1 hi)),
    Finset.card_range] at partition
  exact ⟨c, partition⟩

/-- Masking a uniform `w`-bit word is exactly uniform on `[0, N)` precisely for
the power-of-two bounds `N = 2^k`, `k ≤ w`. -/
theorem equal_fibers_iff {w N : ℕ} (hN : 0 < N) :
    (∃ c, ∀ i < N, (fiber w N i).card = c) ↔ ∃ k ≤ w, N = 2 ^ k := by
  constructor
  · rintro ⟨c, equal⟩
    exact (Nat.dvd_prime_pow Nat.prime_two).1 (dvd_of_equal_fibers hN equal)
  · rintro ⟨k, hk, rfl⟩
    exact ⟨2 ^ (w - k), fun i hi => fiber_card_pow hk hi⟩

/-- The installed 64-bit instance: every bound `2^k`, `k ≤ 63`, is exact. -/
theorem word64_exact {k i : ℕ} (hk : k ≤ 63) (hi : i < 2 ^ k) :
    (fiber 64 (2 ^ k) i).card = 2 ^ (64 - k) :=
  fiber_card_pow (by omega) hi

/-- A bound that is not a power of two, such as three, is not exact on 64-bit
words: some two residues have different preimage counts. -/
theorem word64_three_inexact : ¬ ∃ c, ∀ i < 3, (fiber 64 3 i).card = c := by
  rintro ⟨c, equal⟩
  exact absurd (dvd_of_equal_fibers (by decide) equal) (by decide)

end Zkc.Probability.UniformIndex
