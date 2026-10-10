import Zkc.Probability.Observation
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Abel

/-! Affine mask translations that preserve a selected observation history.

Conditional masses retain impossible conditioning events explicitly. A
history-dependent translation also preserves the stated continuation observer.
-/

set_option autoImplicit false

namespace Zkc.Probability.FramedMask
variable {G H V O : Type} [AddCommGroup G] [AddCommGroup H] [AddCommGroup V]

-- C is an explicitly chosen visible history / retained continuation frame.
-- Its adequacy for a concrete source is a separate interpretation obligation.
def framedRange (A : G →+ V) (C : G →+ H) (c : H) (b : V) : Set V :=
  {y | ∃ r, C r = c ∧ y = A r + b}

theorem framed_range_iff (A : G →+ V) (C : G →+ H) (r₀ : G) (b d : V) :
    framedRange A C (C r₀) b = framedRange A C (C r₀) d ↔
      ∃ u, C u = 0 ∧ b - d = A u := by
  constructor
  · intro he
    have hb : A r₀ + b ∈ framedRange A C (C r₀) b := ⟨r₀, rfl, rfl⟩
    rw [he] at hb
    obtain ⟨r, hc, ha⟩ := hb
    refine ⟨r - r₀, by simp [map_sub, hc], ?_⟩
    rw [map_sub]
    have hh : b = A r + d - A r₀ := by rw [← ha]; abel
    rw [hh]; abel
  · rintro ⟨u, hc, hu⟩
    have hb : b = A u + d := by rw [← hu]; abel
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r + u, by simp [map_add, hr, hc], by simp [map_add, hb, add_assoc]⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r - u, by simp [map_sub, hr, hc], ?_⟩
      simp only [map_sub, hb]; abel

abbrev conditionalFiber (A : G →+ V) (C : G →+ H) (c : H) (b y : V) :=
  {r : G // C r = c ∧ A r + b = y}

def conditionalFiberShift (A : G →+ V) (C : G →+ H) (c : H) (b d : V)
    (u : G) (hc : C u = 0) (hu : b - d = A u) (y : V) :
    conditionalFiber A C c b y ≃ conditionalFiber A C c d y where
  toFun r := ⟨r.val + u, by
    constructor
    · simpa [map_add, hc] using r.property.1
    · have hb : b = A u + d := by rw [← hu]; abel
      simpa [map_add, hb, add_assoc] using r.property.2⟩
  invFun r := ⟨r.val - u, by
    constructor
    · simpa [map_sub, hc] using r.property.1
    · have hb : b = A u + d := by rw [← hu]; abel
      have hh : A (r.val - u) + b = A r.val + d := by
        simp only [map_sub, hb]; abel
      rw [hh]; exact r.property.2⟩
  left_inv r := by apply Subtype.ext; simp
  right_inv r := by apply Subtype.ext; simp

-- Impossible conditioning events have no probability value.
def conditionalMass [Fintype G] [DecidableEq H] [DecidableEq V]
    (A : G →+ V) (C : G →+ H) (c : H) (b y : V) : Option ℚ :=
  let den := Fintype.card {r : G // C r = c}
  if den = 0 then none else
    some ((Fintype.card (conditionalFiber A C c b y) : ℚ) / den)

theorem conditional_mass_preserved [Fintype G] [DecidableEq H] [DecidableEq V]
    (A : G →+ V) (C : G →+ H) (c : H) (b d : V)
    (u : G) (hc : C u = 0) (hu : b - d = A u) (y : V) :
    conditionalMass A C c b y = conditionalMass A C c d y := by
  unfold conditionalMass
  rw [Fintype.card_congr (conditionalFiberShift A C c b d u hc hu y)]

-- The proof may choose a different translation for each public history.
-- C(u(c)) = 0 makes this choice invertible, even though u is not linear.
def historyShift (C : G →+ H) (u : H → G) (r : G) := r + u (C r)

theorem history_preserved (C : G →+ H) (u : H → G)
    (hc : ∀ c, C (u c) = 0) (r : G) : C (historyShift C u r) = C r := by
  simp [historyShift, map_add, hc]

def historyEquiv (C : G →+ H) (u : H → G) (hc : ∀ c, C (u c) = 0) : G ≃ G where
  toFun := historyShift C u
  invFun r := r - u (C r)
  left_inv r := by simp [historyShift, map_add, hc]
  right_inv r := by simp [historyShift, map_sub, hc]

theorem history_shift_bijective (C : G →+ H) (u : H → G)
    (hc : ∀ c, C (u c) = 0) : Function.Bijective (historyShift C u) :=
  (historyEquiv C u hc).bijective

theorem history_observation_preserved (A : G →+ V) (C : G →+ H)
    (b d : H → V) (u : H → G) (hc : ∀ c, C (u c) = 0)
    (hu : ∀ c, b c - d c = A (u c)) (r : G) :
    A r + b (C r) = A (historyShift C u r) + d (C (historyShift C u r)) := by
  rw [history_preserved C u hc]
  have hb : b (C r) = A (u (C r)) + d (C r) := by rw [← hu]; abel
  simp [historyShift, map_add, hb, add_assoc]

-- Any deterministic continuation restricted to this pair is covered.
-- Additional randomness can be a separately fixed argument to k. No assertion
-- about arbitrary contexts that inspect more of r follows from this theorem.
theorem continuation_preserved (A : G →+ V) (C : G →+ H)
    (b d : H → V) (u : H → G) (hc : ∀ c, C (u c) = 0)
    (hu : ∀ c, b c - d c = A (u c)) (k : H → V → O) (r : G) :
    k (C r) (A r + b (C r)) =
      k (C (historyShift C u r))
        (A (historyShift C u r) + d (C (historyShift C u r))) := by
  rw [← history_observation_preserved A C b d u hc hu, history_preserved C u hc]

theorem continuation_mass_preserved [Fintype G] [DecidableEq O]
    (A : G →+ V) (C : G →+ H) (b d : H → V) (u : H → G)
    (hc : ∀ c, C (u c) = 0) (hu : ∀ c, b c - d c = A (u c))
    (k : H → V → O) (o : O) :
    (Fintype.card {r : G // k (C r) (A r + b (C r)) = o} : ℚ) / Fintype.card G =
    (Fintype.card {r : G // k (C r) (A r + d (C r)) = o} : ℚ) / Fintype.card G := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv (historyEquiv C u hc)
    (fun r => k (C r) (A r + b (C r)))
    (fun r => k (C r) (A r + d (C r)))
    (continuation_preserved A C b d u hc hu k) o)]

end Zkc.Probability.FramedMask
