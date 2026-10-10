import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators
namespace Zkc.Probability.FiniteKernel

/-- Unnormalized JOINT mass of controller view v and hidden provider state h.
    Request and stop decisions are functions of v, including captured setup. -/
def viewMass {V H : Type} [Fintype H] (μ : V → H → ℚ) (v : V) : ℚ :=
  ∑ h, μ v h

/-- K includes both the next output and successor hidden state. -/
def outputMass {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (v : V) (d : D) : ℚ :=
  ∑ h, ∑ h', μ v h * K v h d h'

/-- A persistent provider's useful law is a posterior mixture law, not a
    bound on each fixed hidden seed (which may be deterministic). -/
def JointCap {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (ε : V → ℚ) : Prop :=
  ∀ v d, outputMass μ K v d ≤ ε v * viewMass μ v

/-- Exact conditional-law theorem for arbitrary finite rational joint mass.
    The factorization must be derived for the actual transition K. -/
theorem conditional_of_joint {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ)
    (ν : V → D → ℚ)
    (law : ∀ v d, outputMass μ K v d = viewMass μ v * ν v d)
    (v : V) (positive : 0 < viewMass μ v) (d : D) :
    outputMass μ K v d / viewMass μ v = ν v d := by
  rw [law]
  exact mul_div_cancel_left₀ _ (ne_of_gt positive)

/-- Point-mass cap conditional on every positive-mass full view. -/
theorem conditional_cap {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (ε : V → ℚ)
    (cap : JointCap μ K ε) (v : V) (positive : 0 < viewMass μ v) (d : D) :
    outputMass μ K v d / viewMass μ v ≤ ε v := by
  exact (div_le_iff₀ positive).mpr (cap v d)

/-- The controller selects an arbitrary finite bad set from its full view.
    Summing its point masses costs the cardinality of that selected set. -/
theorem adaptive_bad_set {V H D : Type} [Fintype H] [DecidableEq D]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (ε : V → ℚ)
    (cap : JointCap μ K ε) (bad : V → Finset D) (v : V) :
    (∑ d ∈ bad v, outputMass μ K v d) ≤
      (bad v).card * ε v * viewMass μ v := by
  calc
    _ ≤ ∑ _d ∈ bad v, ε v * viewMass μ v :=
      Finset.sum_le_sum (fun d _ => cap v d)
    _ = _ := by simp [mul_assoc]

/-- A pre-draw stopping rule selects entire view fibers. We retain refusal
    probability instead of conditioning on acceptance after seeing the draw. -/
theorem stopped_adaptive_bound {V H D : Type} [Fintype V] [Fintype H] [DecidableEq D]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (ε : V → ℚ)
    (cap : JointCap μ K ε) (bad : V → Finset D) (active : V → Bool) :
    (∑ v, if active v then ∑ d ∈ bad v, outputMass μ K v d else 0) ≤
      ∑ v, if active v then (bad v).card * ε v * viewMass μ v else 0 := by
  apply Finset.sum_le_sum
  intro v _
  split
  · exact adaptive_bad_set μ K ε cap bad v
  · exact le_rfl

/-- Caps survive coarsening by summing fibers; the reverse is false.
    This is the finite tower-property inequality without division by zero. -/
theorem coarsen_cap {V H D W : Type} [Fintype V] [Fintype H] [DecidableEq W]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (ε : ℚ)
    (cap : JointCap μ K (fun _ => ε)) (f : V → W) (w : W) (d : D) :
    (∑ v, if f v = w then outputMass μ K v d else 0) ≤
      ε * ∑ v, if f v = w then viewMass μ v else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : f v = w
  · simpa [hv] using cap v d
  · simp [hv]

/-- Sufficient stronger law: every possible hidden state has a capped output
    kernel. Useful with renewed entropy; intentionally too strong for tapes. -/
theorem statewise_implies_joint {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (ε : V → ℚ)
    (nonneg : ∀ v h, 0 ≤ μ v h)
    (localcap : ∀ v h d, (∑ h', K v h d h') ≤ ε v) : JointCap μ K ε := by
  intro v d
  unfold outputMass viewMass
  calc
    _ = ∑ h, μ v h * ∑ h', K v h d h' := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
    _ ≤ ∑ h, μ v h * ε v := Finset.sum_le_sum (fun h _ =>
      mul_le_mul_of_nonneg_left (localcap v h d) (nonneg v h))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Kernel mass conservation: the joint update really preserves view mass
    when each hidden-state transition is normalized. -/
theorem output_normalized {V H D : Type} [Fintype H] [Fintype D]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ)
    (norm : ∀ v h, (∑ d, ∑ h', K v h d h') = 1) (v : V) :
    (∑ d, outputMass μ K v d) = viewMass μ v := by
  unfold outputMass viewMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp_rw [← Finset.mul_sum]
  rw [norm, mul_one]

/-- General positive law: setup, old outputs and controller coins may all be
    arbitrary functions of x. Only the NEXT coordinate must factor from x.
    This algebra applies to every finite X, D, V, with arbitrary rational weights. -/
theorem independent_coordinate {X D V : Type} [Fintype X] [DecidableEq V]
    (w : X → ℚ) (p : D → ℚ) (view : X → V) (v : V) (d : D) :
    (∑ x, if view x = v then w x * p d else 0) =
      (∑ x, if view x = v then w x else 0) * p d := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : view x = v <;> simp [hx]

theorem independent_coordinate_conditional {X D V : Type}
    [Fintype X] [DecidableEq V]
    (w : X → ℚ) (p : D → ℚ) (view : X → V) (v : V) (d : D)
    (positive : 0 < ∑ x, if view x = v then w x else 0) :
    (∑ x, if view x = v then w x * p d else 0) /
      (∑ x, if view x = v then w x else 0) = p d := by
  rw [independent_coordinate]
  exact mul_div_cancel_left₀ _ (ne_of_gt positive)

/-- The successor joint state must be carried forward, not resampled from the
    original seed law after each call. The request is already included in v. -/
def update {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (v : V) (d : D) (h' : H) : ℚ :=
  ∑ h, μ v h * K v h d h'

theorem update_output_mass {V H D : Type} [Fintype H]
    (μ : V → H → ℚ) (K : V → H → D → H → ℚ) (v : V) (d : D) :
    (∑ h', update μ K v d h') = outputMass μ K v d := by
  exact Finset.sum_comm

end Zkc.Probability.FiniteKernel
