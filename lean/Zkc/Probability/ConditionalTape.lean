import Zkc.Probability.ProductTape

set_option autoImplicit false

namespace PIR.ProductTape
open ENNReal

variable {D S E A : Type} {J : Signature}

abbrev View (D S E A : Type) := Execution (S × Nat) (Sum D E) A

/-- A decision on the FULL pre-draw view; no post-draw conditioning. Previous
    terminal stops stay terminal. A declined fresh request is an explicit abort. -/
def request (active : View D S E A → Bool) (v : View D S E A) : Proc (sig D J) D :=
  match v.outcome with
  | .stopped why => .halt why
  | .returned _ => if active v then .call none .done else .halt .abort

def requesting (active : View D S E A → Bool) (v : View D S E A) : Bool :=
  match v.outcome with
  | .stopped _ => false
  | .returned _ => active v && (v.state.2 != 0)

/-- Actual finite persistent execution, then a view-selected request at its
    retained state. The observation retains the full checkpoint and next outcome. -/
noncomputable def nextJoint (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) (active : View D S E A → Bool) :
    PMF (View D S E A × Outcome D) := do
  let actual ← expand q st >>= p.runM (persistent localH)
  let next ← (request active (checkpoint actual)).runM (persistent localH) actual.state
  pure (checkpoint actual,next.outcome)

theorem next_joint_exact (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) (active : View D S E A → Bool) :
    nextJoint q localH p st active = (do
      let v ← p.runM (online q localH) st
      let next ← (request active v).runM (online q localH) v.state
      pure (v,next.outcome)) := by
  unfold nextJoint
  rw [execution_expand, bind_assoc]
  congr 1
  funext v
  rw [reconstruct_use q v (fun view actual => do
    let next ← (request active view).runM (persistent localH) actual.state
    pure (view,next.outcome))]
  simp only [Execution.expand, bind_assoc, pure_bind]
  rw [← bind_assoc, execution_expand, bind_assoc]
  congr 1
  funext r
  exact outcome_expand q r (fun out => pure (v,out))

theorem pair_mass {X Y Z : Type} (p : PMF X) (f : X → PMF Y) (obs : Y → Z)
    (x : X) (z : Z) :
    ((do let v ← p; let y ← f v; pure (v,obs y)) : PMF (X × Z)) (x,z) =
      p x * (obs <$> f x) z := by
  classical
  let : DecidableEq X := Classical.typeDecidableEq X
  let : DecidableEq Z := Classical.typeDecidableEq Z
  have inner (v : X) :
      ((f v).bind fun y => PMF.pure (v,obs y)) (x,z) =
        if v = x then (obs <$> f v) z else 0 := by
    change ((f v).map (fun y => (v,obs y))) (x,z) = _
    simp only [PMF.monad_map_eq_map, PMF.map_apply, Prod.mk.injEq]
    by_cases h : v = x
    · simp [h]
    · simp [h, Ne.symm h]
  change (p.bind fun v => (f v).bind fun y => PMF.pure (v,obs y)) (x,z) = _
  simp only [PMF.bind_apply, inner, mul_ite, mul_zero, tsum_ite_eq]

/-- Exact conditional numerator, including stopped/exhausted/declined fibers. -/
theorem next_mass (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) (active : View D S E A → Bool)
    (v : View D S E A) (d : D) :
    nextJoint q localH p st active (v,.returned d) =
      (p.runM (online q localH) st) v *
        (if requesting active v then q d else 0) := by
  classical
  let : DecidableEq D := Classical.typeDecidableEq D
  have pure_eq {X : Type} (x : X) : (pure x : PMF X) = PMF.pure x := rfl
  have bind_eq {X Y : Type} (p : PMF X) (f : X → PMF Y) :
      (p >>= f) = p.bind f := rfl
  rw [next_joint_exact, pair_mass]
  congr 1
  rcases v with ⟨out,⟨s,n⟩,es⟩
  cases out with
  | stopped why => simp [request, requesting, Proc.runM, pure_eq, PMF.monad_map_eq_map,
      PMF.pure_map, PMF.pure_apply]
  | returned a =>
    by_cases ha : active ⟨.returned a,(s,n),es⟩ = true
    · cases n <;> simp [request, requesting, Proc.runM, online, Execution.followM, ha,
        pure_eq, bind_eq, PMF.monad_map_eq_map, PMF.map, PMF.pure_apply]
    · simp [request, requesting, ha, Proc.runM, pure_eq, PMF.monad_map_eq_map, PMF.pure_map,
        PMF.pure_apply]

theorem conditional_next (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) (active : View D S E A → Bool)
    (v : View D S E A) (positive : (p.runM (online q localH) st) v ≠ 0)
    (enabled : requesting active v = true) (d : D) :
    nextJoint q localH p st active (v,.returned d) /
      (p.runM (online q localH) st) v = q d := by
  rw [next_mass, if_pos enabled, mul_comm]
  exact ENNReal.mul_div_cancel_right positive (ne_of_lt (PMF.apply_lt_top _ _))

/-- The actual posterior point cap, derived from the product source law.
    Non-requesting and exhausted fibers contribute zero success mass. -/
theorem joint_cap (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) (active : View D S E A → Bool)
    (ε : ℝ≥0∞) (cap : ∀ d, q d ≤ ε) (v : View D S E A) (d : D) :
    nextJoint q localH p st active (v,.returned d) ≤
      ε * (p.runM (online q localH) st) v := by
  rw [next_mass, mul_comm]
  apply mul_le_mul_left
  split
  · exact cap d
  · exact zero_le

theorem mass_bind_le {X Y : Type} (p : PMF X) (f : X → PMF Y) (y : Y) (ε : ℝ≥0∞)
    (bound : ∀ x ∈ p.support, f x y ≤ ε) : (p.bind f) y ≤ ε := by
  classical
  let : DecidableEq ℝ≥0∞ := Classical.typeDecidableEq _
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' x, p x * ε := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : p x = 0
      · simp [hx]
      · exact mul_le_mul' le_rfl (bound x hx)
    _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem next_normalized (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) A) (st : S × Nat) (active : View D S E A → Bool) :
    ∑' result, nextJoint q localH p st active result = 1 :=
  PMF.tsum_coe _

end PIR.ProductTape
