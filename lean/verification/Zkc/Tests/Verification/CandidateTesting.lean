import Zkc.Protocol.Library.Families.Stark.CandidateTesting
import Mathlib.Algebra.Field.ZMod
import Zkc.Tools.Program.DeclarationAudit

/-! Controls distinguish domain violation, candidate-list loss and the universal
candidate quantifier. These do not assert a completed STARK source theorem. -/

namespace TestsSecurity.CandidateTesting
open Polynomial OracleComp ZkcSecurity.Families.Stark
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable local instance : SampleableType (ZMod 3) := SampleableType.ofFintype _
noncomputable local instance : SampleableType ↥(Finset.univ : Finset (ZMod 3)) :=
  SampleableType.finsetCoe _ ⟨0, Finset.mem_univ _⟩

/-- A nonzero constraint polynomial may still vanish on the whole AIR domain.
That hypothesis alone cannot rule out an exact quotient. -/
theorem nonzero_is_not_domain_violation :
    (X : Polynomial (ZMod 3)) ≠ 0 ∧
      residual ({0} : Finset (ZMod 3)) X 1 = 0 := by
  constructor
  · exact X_ne_zero
  · simp [ZkcSecurity.Families.Stark.residual, vanishing, Lagrange.nodal]

/-- Three individually nonzero linear candidates cover every challenge. -/
theorem candidate_union_probability :
    Pr{let x ← $ᵗ (ZMod 3)}[
      ∃ c : ZMod 3, (X - C c : Polynomial (ZMod 3)).eval x = 0] = 1 := by
  apply (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr
  intro x
  exact ⟨x, by simp⟩

/-- The same family has no identically zero candidate. -/
theorem candidate_nonzero (c : ZMod 3) : (X - C c : Polynomial (ZMod 3)) ≠ 0 := by
  intro h
  have coeff := congrArg (fun p : Polynomial (ZMod 3) ↦ p.coeff 1) h
  simp at coeff

/-- A bound for one candidate cannot be reused for an adaptively chosen list member. -/
theorem omit_list_loss_false :
    ¬ Pr{let x ← $ᵗ (ZMod 3)}[
      ∃ c : ZMod 3, (X - C c : Polynomial (ZMod 3)).eval x = 0] ≤ 1 / 3 := by
  rw [candidate_union_probability]
  norm_num

/-- The quantified family theorem counts all three candidates and remains valid. -/
theorem simultaneous_candidate_bound :
    Pr{let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      ∃ c ∈ (Finset.univ : Finset (ZMod 3)),
        (X - C c : Polynomial (ZMod 3)).eval (x : ZMod 3) = 0] ≤ 1 := by
  have bound := candidate_roots_uniform_le (Finset.univ : Finset (ZMod 3))
    (fun c ↦ X - C c) (fun c _ ↦ candidate_nonzero c)
    (degree := 1) (fun c _ ↦ by simp) (Finset.univ : Finset (ZMod 3))
  norm_num only [Finset.card_univ, ZMod.card, Nat.reduceSub, Nat.cast_ofNat] at bound
  have ratio : (3 : ℝ≥0∞) / 3 = 1 := ENNReal.div_self (by norm_num) (by finiteness)
  simpa only [mul_one_div, ratio] using bound

/-- Choosing the quotient after alpha is permitted. Only its pre-evaluation
list size and residual degree are assumed here. -/
theorem adaptive_quotient_bound
    (quotients : ZMod 3 → Finset (Polynomial (ZMod 3)))
    (size : ∀ a, (quotients a).card ≤ 1)
    (degree : ∀ a q, q ∈ quotients a →
      (residual {0} (powerBatch (fun _ : Fin 2 ↦ C 1) a) q).natDegree ≤ 1) :
    Pr{let a ← $ᵗ (ZMod 3); let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      ∃ q ∈ quotients a,
        (residual {0} (powerBatch (fun _ : Fin 2 ↦ C 1) a) q).eval (x : ZMod 3) = 0]
        ≤ 2 / 3 := by
  have bound := adaptive_quotient_candidates_uniform_le {0} (fun _ : Fin 2 ↦ C 1)
    ⟨0, by simp, 0, by simp⟩ quotients size degree (Finset.univ : Finset (ZMod 3))
  norm_num only [Finset.card_univ, ZMod.card, Nat.reduceSub, Nat.cast_ofNat, one_mul] at bound
  simpa only [ENNReal.div_add_div_same, one_add_one_eq_two] using bound

/-- Three fixed AIR assignments, indexed by the field before either challenge. -/
noncomputable def traceConstraints (trace : ZMod 3) : Fin 2 → Polynomial (ZMod 3) :=
  fun i ↦ if i = 0 then C (-trace) else 1

/-- Each assignment violates the AIR at zero through its second constraint. -/
theorem trace_constraints_invalid (trace : ZMod 3) :
    ∃ point ∈ ({0} : Finset (ZMod 3)), ∃ i, (traceConstraints trace i).eval point ≠ 0 := by
  exact ⟨0, by simp, 1, by simp [traceConstraints]⟩

/-- The zero quotient leaves a constant residual, vanishing exactly when alpha is the trace. -/
theorem trace_residual (trace alpha : ZMod 3) :
    residual {0} (powerBatch (traceConstraints trace) alpha) 0 = C (alpha - trace) := by
  simp [ZkcSecurity.Families.Stark.residual, powerBatch, Fin.sum_univ_two,
    traceConstraints, sub_eq_add_neg, add_comm]

/-- The fixed family of three invalid assignments covers every batching challenge. -/
theorem trace_union_probability :
    Pr{let a ← $ᵗ (ZMod 3); let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      ∃ trace ∈ (Finset.univ : Finset (ZMod 3)), ∃ q ∈ ({0} : Finset (Polynomial (ZMod 3))),
        (residual {0} (powerBatch (traceConstraints trace) a) q).eval (x : ZMod 3) = 0] =
      1 := by
  simp [trace_residual, sub_eq_zero]

/-- The trace-family theorem pays all three batching losses, with one quotient and degree zero. -/
theorem simultaneous_trace_bound :
    Pr{let a ← $ᵗ (ZMod 3); let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      ∃ trace ∈ (Finset.univ : Finset (ZMod 3)), ∃ q ∈ ({0} : Finset (Polynomial (ZMod 3))),
        (residual {0} (powerBatch (traceConstraints trace) a) q).eval (x : ZMod 3) = 0] ≤
      1 := by
  have bound := trace_quotient_candidates_uniform_le (Finset.univ : Finset (ZMod 3))
    {0} traceConstraints (fun trace _ ↦ trace_constraints_invalid trace)
    (fun _ _ ↦ {0}) (listBound := 1) (degree := 0) (by simp)
    (by simp [trace_residual]) (Finset.univ : Finset (ZMod 3))
  convert bound using 1
  norm_num
  exact (ENNReal.mul_inv_cancel (by norm_num) (by finiteness)).symm

/-- Removing the outer trace cardinality would incorrectly bound probability one by one third. -/
theorem omit_trace_loss_false :
    ¬ Pr{let a ← $ᵗ (ZMod 3); let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      ∃ trace ∈ (Finset.univ : Finset (ZMod 3)), ∃ q ∈ ({0} : Finset (Polynomial (ZMod 3))),
        (residual {0} (powerBatch (traceConstraints trace) a) q).eval (x : ZMod 3) = 0] ≤
      1 / 3 := by
  rw [trace_union_probability]
  norm_num

/-- With no traces the same theorem bounds the empty collision event by zero. -/
theorem empty_trace_family_bound :
    Pr{let a ← $ᵗ (ZMod 3); let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      ∃ trace ∈ (∅ : Finset (ZMod 3)), ∃ q ∈ ({0} : Finset (Polynomial (ZMod 3))),
        (residual {0} (powerBatch (traceConstraints trace) a) q).eval (x : ZMod 3) = 0] ≤
      0 := by
  simpa only [Finset.card_empty, Nat.cast_zero, zero_mul] using
    trace_quotient_candidates_uniform_le (∅ : Finset (ZMod 3)) {0} traceConstraints
      (by simp) (fun _ _ ↦ {0}) (listBound := 1) (degree := 0) (by simp) (by simp)
      (Finset.univ : Finset (ZMod 3))

/-- An existential mismatch is compatible with every component having a good candidate. -/
theorem existential_mismatch_does_not_separate :
    (∀ answer : ZMod 3, ∃ candidate : ZMod 3, candidate ≠ answer) ∧
      ¬ (∃ answer : ZMod 3, ∀ candidate : ZMod 3, candidate ≠ answer) := by
  decide

/-- Empty candidate families satisfy universal disagreement without inventing
an element; the later quotient theorem still requires its own domain premises. -/
theorem empty_candidate_family :
    ∃ _i : Unit, ∀ c ∈ (∅ : Set (ZMod 3)), ¬ (c = 0) := by
  exact ⟨(), by simp⟩

end TestsSecurity.CandidateTesting

run_cmd ZkcTools.DeclarationAudit.check [`Zkc.Protocol.Library.Families.Stark.CandidateTesting] "CANDIDATE-TESTING-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "CANDIDATE-CONTROLS-AXIOMS-PASS"
