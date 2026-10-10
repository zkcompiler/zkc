import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Randomized opening-degree correction over arbitrary finite words.

Multiplication by X alone does not establish a committed word's degree bound.
The two-correction algebraic lemma supports testing D and X*D in a fresh
random linear combination. Turning FRI acceptance into common agreement is a separate
proximity obligation; no cryptographic security theorem is asserted here. -/

set_option autoImplicit false

namespace Zkc.Polynomial.DegreeAdjustment
open _root_.Polynomial
variable {F : Type*} [Field F]

/-- For nonzero polynomials the adjustment increases the degree by exactly one.
The zero case is separate because its natural degree is defined to be zero. -/
theorem degree_iff (p : F[X]) (hp : p ≠ 0) (bound : ℕ) :
    (X * p).natDegree < bound ↔ p.natDegree + 1 < bound := by
  rw [natDegree_X_mul hp]

/-- Scaling by a nonzero domain coordinate preserves exact agreement. -/
theorem agreement_iff (x a b : F) (hx : x ≠ 0) :
    x * a = x * b ↔ a = b := ⟨mul_left_cancel₀ hx, congrArg (x * ·)⟩

/-- The adjustment cannot remove an opening pole away from zero. -/
theorem opening_divisor_iff (p : F[X]) (z : F) (hz : z ≠ 0) :
    X - C z ∣ X * p ↔ X - C z ∣ p := by
  simp [dvd_iff_isRoot, IsRoot, hz]


/-- Two distinct successful corrections on a common set larger than the code
capacity give a representative with one less degree of freedom. `word` is an
arbitrary function, not an assumed low-degree polynomial. The zero case is
explicit because `natDegree 0 = 0`. This is an exact agreement statement. -/
theorem exists_strict_representative_of_two_corrections (s : Finset F) (n : ℕ) (hs : n < s.card)
    (word : F → F) (a b : F) (hab : a ≠ b) (p₀ p₁ : F[X])
    (h₀ : p₀.natDegree < n) (h₁ : p₁.natDegree < n)
    (e₀ : ∀ x ∈ s, p₀.eval x = (1 + a * x) * word x)
    (e₁ : ∀ x ∈ s, p₁.eval x = (1 + b * x) * word x) :
    ∃ q : F[X], (q = 0 ∨ q.natDegree + 1 < n) ∧ ∀ x ∈ s, q.eval x = word x := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  let r := C (b - a)⁻¹ * (p₁ - p₀)
  let q := p₀ - C a * r
  have hr : r.natDegree < n :=
    (natDegree_C_mul_le _ _).trans_lt
      ((natDegree_sub_le _ _).trans_lt (max_lt h₁ h₀))
  have hq : q.natDegree < n :=
    (natDegree_sub_le _ _).trans_lt (max_lt h₀ ((natDegree_C_mul_le _ _).trans_lt hr))
  have er (x : F) (hx : x ∈ s) : r.eval x = x * word x := by
    simp only [r, eval_mul, eval_C, eval_sub, e₀ x hx, e₁ x hx]
    field_simp
    ring
  have eq (x : F) (hx : x ∈ s) : q.eval x = word x := by
    simp only [q, eval_sub, eval_mul, eval_C, e₀ x hx, er x hx]
    ring
  have hXq : (X * q).natDegree ≤ n := by
    by_cases hz : q = 0
    · simp [hz]
    · rw [natDegree_X_mul hz]
      omega
  have identity : X * q = r := by
    apply eq_of_natDegree_lt_card_of_eval_eq' _ _ s
    · intro x hx
      simp only [eval_mul, eval_X, eq x hx, er x hx]
    · exact max_lt (hXq.trans_lt hs) (hr.trans hs)
  refine ⟨q, ?_, eq⟩
  by_cases hz : q = 0
  · exact Or.inl hz
  · right
    rw [← natDegree_X_mul hz, identity]
    exact hr

/-- Honest strict representatives satisfy every linear correction, including
zero challenges and correction factors that vanish at a domain point. -/
theorem exists_corrected_representative (s : Finset F) (n : ℕ) (hn : 0 < n)
    (word : F → F) (q : F[X]) (hq : q = 0 ∨ q.natDegree + 1 < n)
    (heval : ∀ x ∈ s, q.eval x = word x) (rho : F) :
    ∃ p : F[X], p.natDegree < n ∧
      ∀ x ∈ s, p.eval x = (1 + rho * x) * word x := by
  have hX : (X * q).natDegree < n := by
    rcases hq with hz | hd
    · simpa [hz] using hn
    · by_cases hz : q = 0
      · simpa [hz] using hn
      · simpa [natDegree_X_mul hz] using hd
  have hq' : q.natDegree < n := by
    rcases hq with hz | hd
    · simpa [hz] using hn
    · omega
  refine ⟨q + C rho * (X * q), ?_, ?_⟩
  · exact (natDegree_add_le _ _).trans_lt
      (max_lt hq' ((natDegree_C_mul_le _ _).trans_lt hX))
  · intro x hx
    simp only [eval_add, eval_mul, eval_C, eval_X, heval x hx]
    ring

/-- Outside the strict code, at most one correction can have exact low-degree
agreement on this fixed set. This does not turn sampled FRI acceptance into
exact code membership. -/
theorem correction_unique_of_no_strict_representative
    (s : Finset F) (n : ℕ) (hs : n < s.card) (word : F → F)
    (hbad : ¬ ∃ q : F[X], (q = 0 ∨ q.natDegree + 1 < n) ∧
      ∀ x ∈ s, q.eval x = word x)
    (a b : F) (p₀ p₁ : F[X]) (h₀ : p₀.natDegree < n) (h₁ : p₁.natDegree < n)
    (e₀ : ∀ x ∈ s, p₀.eval x = (1 + a * x) * word x)
    (e₁ : ∀ x ∈ s, p₁.eval x = (1 + b * x) * word x) : a = b := by
  by_contra hab
  exact hbad (exists_strict_representative_of_two_corrections
    s n hs word a b hab p₀ p₁ h₀ h₁ e₀ e₁)

end Zkc.Polynomial.DegreeAdjustment
