module

public import Zkc.Formal.Interactive.Reduction

@[expose] public section

namespace Zkc.Formal.Interactive.Sumcheck
open Core

/-- A public Boolean-cube table split on the most significant variable. -/
@[reducible] def Cube (F : Type) : Nat → Type
  | 0 => F
  | n+1 => Cube F n × Cube F n

namespace Cube
open Lean.Grind
variable {F : Type} [CommRing F]

def sum : (n : Nat) → Cube F n → F
  | 0, x => x
  | n+1, t => sum n t.1 + sum n t.2

/-- Pointwise interpolation of the two halves. -/
def interpolate (r : F) : (n : Nat) → Cube F n → Cube F n → Cube F n
  | 0, a, b => (a : F) + ((b : F)-(a : F))*r
  | n+1, a, b => (interpolate r n a.1 b.1, interpolate r n a.2 b.2)

def restrict (n : Nat) (table : Cube F (n+1)) (r : F) : Cube F n :=
  interpolate r n table.1 table.2

theorem sum_interpolate (r : F) (n : Nat) (a b : Cube F n) :
    sum n (interpolate r n a b) = line (sum n a, sum n b) r := by
  induction n with
  | zero =>
    simp only [sum, interpolate, line_normalForm]
    rw [CommSemiring.mul_comm]
  | succ n ih =>
    simp only [sum, interpolate, ih, line, Semiring.left_distrib, Semiring.add_assoc,
      AddCommMonoid.add_left_comm]

def claims : Claims F := ⟨Cube F,sum,restrict⟩

/-- Evaluation requires exactly one challenge for each variable. -/
abbrev evaluate := (@claims F _).evaluate

end Cube

namespace Verifier
variable {S : Sig} {H F M σ : Type} [DecidableEq F]

/-- The relation to the public table is needed for every round, including those
reached after arbitrary messages. It mentions no prover-private residual state. -/
theorem reduce_pairs [Lean.Grind.Field F] (v : Verifier (S := S) H F (F × F))
    (K : Experiment S σ) (points : List F) (distinct : points.Nodup) (positive : 0 < points.length)
    (ends : ∀ m, v.boundary m = m.1 + m.2) (atPoint : ∀ m r, v.evaluate m r = line m r)
    (fresh : v.publicCoins K points positive) (n : Nat) (table : Cube F n)
    (history : List F) (claim : F) (s : σ) (wrong : claim ≠ Cube.sum n table) :
    K.probability (v.reduce n history claim) s (fun (rs, value) _ => decide (Cube.evaluate n table rs = some value)) ≤
      (n : Mass) * roundCost 1 points := by
  apply v.reduce_sound Cube.claims K points positive 1 _ fresh n table history claim s wrong
  intro remaining publicTable asserted m wrongClaim passed
  let honest := (Cube.sum remaining publicTable.1,Cube.sum remaining publicTable.2)
  apply count_unique points distinct
  intro r s atR atS
  have wrongSum : m.1 + m.2 ≠ honest.1 + honest.2 := by
    rw [← ends m,passed]
    exact wrongClaim
  apply line_unique_collision m honest r s wrongSum
  · exact (atPoint m r).symm.trans ((of_decide_eq_true atR).trans
      (Cube.sum_interpolate r remaining publicTable.1 publicTable.2))
  · exact (atPoint m s).symm.trans ((of_decide_eq_true atS).trans
      (Cube.sum_interpolate s remaining publicTable.1 publicTable.2))

/-- The final guard accepts exactly when evaluation of the original public table at
the returned point agrees with the value returned by the reduction. -/
def checkTable [Lean.Grind.CommRing F] (v : Verifier (S := S) H F M) (n : Nat)
    (table : Cube F n) (claim : F) : Process S H Unit :=
  (v.reduce n [] claim).bind fun (rs, value) =>
    if Cube.evaluate n table rs = some value then .done () else .halt v.reject

theorem checkTable_sound [Lean.Grind.Field F] (v : Verifier (S := S) H F (F × F))
    (K : Experiment S σ) (points : List F) (distinct : points.Nodup) (positive : 0 < points.length)
    (ends : ∀ m, v.boundary m = m.1 + m.2) (atPoint : ∀ m r, v.evaluate m r = line m r)
    (fresh : v.publicCoins K points positive) (n : Nat) (table : Cube F n)
    (claim : F) (s : σ) (wrong : claim ≠ Cube.sum n table) :
    K.probability (v.checkTable n table claim) s (fun _ _ => true) ≤ (n : Mass) * roundCost 1 points := by
  have bound := v.reduce_pairs K points distinct positive ends atPoint fresh n table [] claim s wrong
  unfold Experiment.probability at bound ⊢
  simp only [checkTable, Experiment.expect_bind]
  apply Mass.le_trans (K.expect_mono _ _ _ _ ?_) bound
  intro (rs, value) _ _
  by_cases h : Cube.evaluate n table rs = some value <;> simp [Experiment.expect, h]

end Verifier
end Zkc.Formal.Interactive.Sumcheck
