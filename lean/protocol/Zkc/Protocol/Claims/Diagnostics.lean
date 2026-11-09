module

public import Zkc.Protocol.Claims.Problem
public import Zkc.Protocol.Claims.Quantitative

/-!
# Explicit nonvacuity diagnostics

These assessments supplement a receipt. They do not invalidate a kernel proof because of its
proof route. `unchecked` makes absence of evidence visible; it is not a positive assessment.
-/

public section

open scoped ENNReal

namespace ProtocolProof

universe u

/-- An admission population can be witnessed, proved empty, or left unassessed. -/
inductive AdmissionAssessment {E : Type u} (admissible : E → Prop) where
  | inhabited (witness : E) (admitted : admissible witness)
  | empty (proof : ¬ AdmitsInput admissible)
  | unchecked

/-- A uniform probability error bound below one, a vacuous admitted bound, or no assessment. -/
inductive ErrorAssessment {E : Type u} (admissible : E → Prop) (error : E → ℝ≥0∞) where
  | informative (proof : ∀ e, admissible e → error e < 1)
  | vacuous (witness : E) (admitted : admissible witness) (proof : 1 ≤ error witness)
  | unchecked

/-- A finite resource budget, an admitted infinite budget, or no assessment. -/
inductive BudgetAssessment {E : Type u} (admissible : E → Prop) (budget : E → ℝ≥0∞) where
  | finite (proof : ∀ e, admissible e → budget e ≠ ⊤)
  | unbounded (witness : E) (admitted : admissible witness) (proof : budget witness = ⊤)
  | unchecked

/-- Empty admission makes a universal upper claim true; this is precisely why it is reported. -/
theorem UpperRequest.holds_of_empty {E O : Type u} [MeasurableSpace O]
    (request : UpperRequest E O) (empty : ¬ AdmitsInput request.admissible) : request.Holds := by
  intro e he
  exact (empty ⟨e, he⟩).elim

/-- The corresponding fact for honest completeness and other lower-bound claims. -/
theorem LowerRequest.holds_of_empty {E O : Type u} [MeasurableSpace O]
    (request : LowerRequest E O) (empty : ¬ AdmitsInput request.admissible) : request.Holds := by
  intro e he
  exact (empty ⟨e, he⟩).elim

end ProtocolProof
