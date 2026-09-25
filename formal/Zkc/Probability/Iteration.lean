import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring
import Zkc.Semantics.Execution

/-! Complete finite transition laws and conditional retry tails. Finite indices
enumerate outcomes of the actual experiment, including stopped executions;
the infinite stream space is not assumed to be a discrete normalized PMF. -/

set_option autoImplicit false
open scoped BigOperators
namespace Zkc.Probability.Iteration
open PIR
variable {X D V S E A : Type} [Fintype X] [Fintype D] [Fintype V] [DecidableEq V]

/-- Push forward the full transition, including actual state, stop and events.
The chosen next-view function determines what is remembered or disclosed. -/
def transitionMass (mass : X → ℚ) (kernel : X → D → ℚ)
    (record : X → D → Execution S E A)
    (nextView : X → Execution S E A → V) (v : V) : ℚ :=
  ∑ x, ∑ d, if nextView x (record x d) = v then mass x * kernel x d else 0

omit [Fintype V] in
theorem transitionMass_nonneg (mass : X → ℚ) (kernel : X → D → ℚ)
    (record : X → D → Execution S E A) (nextView : X → Execution S E A → V)
    (hm : ∀ x, 0 ≤ mass x) (hk : ∀ x d, 0 ≤ kernel x d) (v : V) :
    0 ≤ transitionMass mass kernel record nextView v := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro d _
  split
  · exact mul_nonneg (hm x) (hk x d)
  · exact le_rfl

theorem transitionMass_total (mass : X → ℚ) (kernel : X → D → ℚ)
    (record : X → D → Execution S E A) (nextView : X → Execution S E A → V)
    (normalized : ∀ x, ∑ d, kernel x d = 1) :
    (∑ v, transitionMass mass kernel record nextView v) = ∑ x, mass x := by
  unfold transitionMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_sum, normalized, mul_one]

/-- Query an event of the pushed-forward complete result. This is a one-step
identity, not permission to reuse an information-losing view as future state. -/
theorem transitionMass_event (mass : X → ℚ) (kernel : X → D → ℚ)
    (record : X → D → Execution S E A) (nextView : X → Execution S E A → V)
    (event : V → Bool) :
    (∑ v, if event v then transitionMass mass kernel record nextView v else 0) =
      ∑ x, ∑ d, if event (nextView x (record x d)) then mass x * kernel x d else 0 := by
  have distribute {Y : Type} [Fintype Y] (p : Bool) (f : Y → ℚ) :
      (if p then ∑ y, f y else 0) = ∑ y, if p then f y else 0 := by
    cases p <;> simp
  unfold transitionMass
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  calc
    _ = ∑ v, if nextView x (record x d) = v then
        (if event v then mass x * kernel x d else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : nextView x (record x d) = v <;> simp [h]
    _ = _ := by simp

/-- A history-conditional continuation bound yields a geometric tail. The
one-step inequality must come from the actual reached joint law (for example
FiniteKernel's posterior mixture cap), not marginal retry probabilities. -/
theorem retry_tail (pending : Nat → ℚ) (q : ℚ) (nonneg : 0 ≤ q)
    (step : ∀ n, pending (n + 1) ≤ q * pending n) (n : Nat) :
    pending n ≤ q ^ n * pending 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      pending (n + 1) ≤ q * pending n := step n
      _ ≤ q * (q ^ n * pending 0) := mul_le_mul_of_nonneg_left ih nonneg
      _ = q ^ (n + 1) * pending 0 := by rw [pow_succ]; ring

/-- Completeness accounting needs an accepted published mass, not merely a
satisfiable constraint system. Fatal and publication failures share `lost`. -/
theorem accepted_lower_bound (accepted pending lost cap lossCap : ℚ)
    (partition : accepted + pending + lost = 1)
    (retryBound : pending ≤ cap) (failureBound : lost ≤ lossCap) :
    1 - cap - lossCap ≤ accepted := by
  have h : pending + lost ≤ cap + lossCap := add_le_add retryBound failureBound
  calc
    1 - cap - lossCap = 1 - (cap + lossCap) := by ring
    _ ≤ 1 - (pending + lost) := sub_le_sub_left h 1
    _ = accepted := by rw [← partition]; ring

end Zkc.Probability.Iteration
