import ZkcArkLib.Stark.OutOfDomain
import ZkcArkLib.Stark.DeepBatching
import Mathlib.Algebra.Field.ZMod
import ZkcTools.DeclarationAudit

namespace TestsArkLib.Stark
open ZkcSecurity.Families.Stark ZkcArkLib.Stark Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open scoped BigOperators

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable local instance : SampleableType (ZMod 3) := SampleableType.ofFintype _

def onePoint : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

theorem complement_size : (outsidePoints onePoint).card = 2 := by
  rw [outsidePoints_card]
  decide

theorem complement_admission : (outsidePoints onePoint).Nonempty :=
  Finset.card_pos.mp (by rw [complement_size]; decide)

theorem nontrivial_ood_error : (1 : ℝ≥0∞) / (Fintype.card (ZMod 3) - Fintype.card (Fin 1) : ℕ) < 1 := by
  simpa only [Nat.cast_one] using outside_error_lt_one onePoint (rootBudget := 1) (by decide)

theorem exact_deep_quotient :
    deepQuotient ({1} : Finset (ZMod 3)) ((Polynomial.X : Polynomial (ZMod 3)) ^ 2) =
      Quotienting.polyQuotient ({1} : Finset (ZMod 3)) ((Polynomial.X : Polynomial (ZMod 3)) ^ 2) :=
  deepQuotient_eq _ _

/-- A real close-probability premise is discharged on a nonempty finite field
and a nonempty evaluation domain, so the affine adapter is not vacuous. -/
theorem affine_zero_joint :
    Code.jointAgreement (C := ReedSolomon.code onePoint 1) (δ := 0)
      (W := fun _ : Fin 2 => (0 : Fin 1 → ZMod 3)) := by
  apply affine_jointAgreement onePoint 1 0 (fun _ => 0) zero_le
  have close : Code.relDistFromCode (0 : Fin 1 → ZMod 3) (ReedSolomon.code onePoint 1) ≤ 0 := by
    have bound := Code.relDistFromCode_le_relDist_to_mem (0 : Fin 1 → ZMod 3) 0
      (Submodule.zero_mem (ReedSolomon.code onePoint 1))
    have self : Code.relHammingDist (0 : Fin 1 → ZMod 3) 0 = 0 := by
      simp [Code.relHammingDist]
    rw [self, ENNReal.coe_NNRat_coe_NNReal] at bound
    simpa using bound
  have all : ∀ challenge : ZMod 3,
      Code.relDistFromCode ((0 : Fin 1 → ZMod 3) + challenge • 0)
        (ReedSolomon.code onePoint 1) ≤ (0 : ℝ≥0) := by
    intro challenge
    simpa using close
  rw [(SampleableType.prEvent_uniformSample_eq_one_iff _).mpr all]
  norm_num [ZMod.card]

def twoPoints : Fin 2 ↪ ZMod 3 := ⟨fun i => i.val, by decide⟩

def spike : Fin 2 → ZMod 3 := ![1, 0]

def threeWords : Fin 3 → Fin 2 → ZMod 3 := ![spike, 0, -spike]

theorem spike_not_codeword : spike ∉ ReedSolomon.code twoPoints 1 := by
  intro member
  obtain ⟨p, degree, evaluates⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp member
  rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp degree)] at evaluates
  have first := evaluates 0
  have second := evaluates 1
  norm_num [spike] at first second
  exact one_ne_zero (first.symm.trans second)

theorem spike_far : (0 : ℝ≥0∞) < Code.relDistFromCode spike (ReedSolomon.code twoPoints 1) := by
  apply lt_of_not_ge
  intro close
  obtain ⟨c, member, distance⟩ :=
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist spike 0).mp close
  have same := (Code.pairRelDist_le_iff_pairDist_le (u := spike) (v := c) 0).mp distance
  have equal : spike = c := by simpa using same
  exact spike_not_codeword (equal ▸ member)

/-- Three genuinely fixed words: gamma = 1 cancels the two far inputs.
This refuses any deterministic claim that a close batch forces close inputs. -/
theorem three_word_bad_at_one :
    Code.relDistFromCode (fun i => ∑ j : Fin 3, (1 : ZMod 3) ^ (j : ℕ) * threeWords j i)
      (ReedSolomon.code twoPoints 1) ≤ (0 : ℝ≥0) ∧
    ∃ j, (0 : ℝ≥0∞) < Code.relDistFromCode (threeWords j) (ReedSolomon.code twoPoints 1) := by
  constructor
  · have batch : (fun i => ∑ j : Fin 3, (1 : ZMod 3) ^ (j : ℕ) * threeWords j i) = 0 := by decide
    rw [batch]
    have bound := Code.relDistFromCode_le_relDist_to_mem (0 : Fin 2 → ZMod 3) 0
      (Submodule.zero_mem (ReedSolomon.code twoPoints 1))
    have self : Code.relHammingDist (0 : Fin 2 → ZMod 3) 0 = 0 := by
      simp [Code.relHammingDist]
    rw [self, ENNReal.coe_NNRat_coe_NNReal] at bound
    simpa using bound
  · exact ⟨0, spike_far⟩

theorem three_word_mca_at_one :
    CoreDefinitions.IsMCA (CoreDefinitions.univariatePowersGenerator (ZMod 3) 2)
      (ReedSolomon.code twoPoints 1) 1 threeWords 0 :=
  powerBatch_bad_implies_isMCA _ 2 threeWords 0 1 three_word_bad_at_one.1 three_word_bad_at_one.2

theorem refuses_omitting_exception :
    ¬ ((0 : ℝ≥0∞) <
      Code.relDistFromCode (fun i => ∑ j : Fin 3, (1 : ZMod 3) ^ (j : ℕ) * threeWords j i)
        (ReedSolomon.code twoPoints 1)) :=
  not_lt_of_ge three_word_bad_at_one.1

/-- The probabilistic adapter accepts an actual three-word instance, including
the exact minimum distance, positive slack and generalized-Johnson radius gate.
This small-field control does not claim that its numerical error is below one. -/
theorem three_word_probability_bound :
    Pr{let gamma ← $ᵗ (ZMod 3)}[
      Code.relDistFromCode (fun i => ∑ j : Fin 3, gamma ^ (j : ℕ) * threeWords j i)
        (ReedSolomon.code twoPoints 1) ≤ (0 : ℝ≥0)] ≤
      powerBatchError 2 3 2 1 (1 / 2) := by
  apply powerBatch_close_uniform_le (ReedSolomon.code twoPoints 1) 2 threeWords 1 (1 / 2) 0
  · decide
  · decide
  · rw [ReedSolomon.minDist_of_le (by decide : 1 ≤ Fintype.card (Fin 2))]
    norm_num
  · norm_num
  · norm_num
  · apply sub_nonneg.mpr
    apply Real.rpow_le_one <;> norm_num
  · exact three_word_bad_at_one.2

theorem refuses_too_many_words : ¬ (3 + 1 ≤ Fintype.card (ZMod 3)) := by decide

theorem refuses_zero_slack : ¬ (0 < (0 : ℝ≥0)) := lt_irrefl _

theorem refuses_wrong_minimum :
    ¬ ((1 / 2 : ℝ) =
      (Code.minDist (ReedSolomon.code twoPoints 1 : Set (Fin 2 → ZMod 3)) : ℝ) /
        Fintype.card (Fin 2)) := by
  rw [ReedSolomon.minDist_of_le (by decide : 1 ≤ Fintype.card (Fin 2))]
  norm_num

theorem refuses_radius_one :
    ¬ ((1 : ℝ) ≤ 1 - (1 - (1 : ℝ) + (1 / 2 : ℝ)) ^ ((1 : ℝ) / (2 + 2))) := by
  have positive : (0 : ℝ) < (1 - (1 : ℝ) + (1 / 2 : ℝ)) ^ ((1 : ℝ) / (2 + 2)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

end TestsArkLib.Stark

run_cmd ZkcTools.DeclarationAudit.check [`ZkcArkLib.Stark] "STARK-ARKLIB-AUDIT-PASS"
run_cmd ZkcTools.DeclarationAudit.checkBoundary [`ZkcArkLib.Stark] [`ArkLib] [] "STARK-ARKLIB-BOUNDARY-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "STARK-ARKLIB-CONTROLS-PASS"
