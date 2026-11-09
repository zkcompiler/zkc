module

public import ProtocolProofExamples.BoundaryControls
public import ProtocolProofExamples.PropertyProfiles

/-!
# Admission, observation, and receipt boundaries

The controls distinguish a promise gap from a negative instance, preserve honest abort mass,
and keep conditional and custom claims separate from established canonical meanings.
-/

public section

open ProtocolProof PFunctor MeasureTheory
open scoped ENNReal

namespace ProtocolProofExamples.ClaimBoundaries

local instance : MeasurableSpace (Option Bool) := ⊤

@[expose] def promise : PromiseProblem Nat where
  yes n := n = 0
  no n := n = 2
  disjoint _ hyes hno := by omega

@[expose] noncomputable def acceptsStatement (statement : Nat) : SoundnessRequest Unit Nat Nat where
  experiment := { run := fun _ ↦ Measure.dirac statement, normalized := fun _ ↦ inferInstance }
  admissible _ := True
  accepts _ := True
  statement := id
  problem := promise
  measurable_bad := MeasurableSet.of_discrete
  error _ := 0

theorem promise_gap_is_not_falsehood : ¬ promise.yes 1 ∧ ¬ promise.no 1 := by
  simp [promise]

theorem accepting_gap_established : (acceptsStatement 1).Holds := by
  intro _ _
  simp [SoundnessRequest.toUpper, acceptsStatement, promise]

theorem accepting_negative_refused : ¬ (acceptsStatement 2).Holds := by
  intro h
  have bad := h () trivial
  simp [SoundnessRequest.toUpper, acceptsStatement, promise] at bad

/-- Returning an adversarially selected negative statement is caught by the output selector. -/
@[expose] noncomputable def adaptiveStatements : SoundnessRequest Nat Nat Nat where
  experiment := { run := fun n ↦ Measure.dirac n, normalized := fun _ ↦ inferInstance }
  admissible _ := True
  accepts _ := True
  statement := id
  problem := promise
  measurable_bad := MeasurableSet.of_discrete
  error _ := 0

theorem adaptive_negative_refused : ¬ adaptiveStatements.Holds := by
  intro h
  have bad := h 2 trivial
  simp [SoundnessRequest.toUpper, adaptiveStatements, promise] at bad

@[expose] noncomputable def honestWithAbort : Experiment Unit (Option Bool) where
  run _ := (2 : ℝ≥0∞)⁻¹ • Measure.dirac (some true) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac none
  normalized _ := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩

@[expose] noncomputable def completeness (error : ℝ≥0∞) :
    CompletenessRequest Unit (Option Bool) where
  experiment := honestWithAbort
  admissible _ := True
  accepts := {some true}
  measurable_accepts := MeasurableSet.of_discrete
  error _ := error

theorem honest_abort_mass : honestWithAbort.run () {none} = (2 : ℝ≥0∞)⁻¹ := by
  simp [honestWithAbort]

theorem honest_half_completeness : (completeness (2 : ℝ≥0∞)⁻¹).Holds := by
  intro _ _
  simp [completeness, CompletenessRequest.toLower, honestWithAbort]

theorem honest_perfect_completeness_refused : ¬ (completeness 0).Holds := by
  intro h
  have bad := h () trivial
  norm_num [completeness, CompletenessRequest.toLower, honestWithAbort] at bad

/-- A requested Boolean observation retains the abort as a rejection, with its probability. -/
@[expose] def acceptedObservation : Observation (Option Bool) Bool where
  observe value := value = some true
  measurable := measurable_of_countable _

theorem observed_abort_preserved :
    (honestWithAbort.observe acceptedObservation).run () {false} = (2 : ℝ≥0∞)⁻¹ := by
  rw [Experiment.observe, Measure.map_apply acceptedObservation.measurable
    MeasurableSet.of_discrete]
  simp [honestWithAbort, acceptedObservation]

theorem soundness_receipt : Receipt (.soundness (acceptsStatement 1)) :=
  ⟨accepting_gap_established⟩

theorem completeness_receipt : Receipt (.completeness (completeness (2 : ℝ≥0∞)⁻¹)) :=
  ⟨honest_half_completeness⟩

theorem recovery_receipt :
    Receipt (.recovery (BoundaryControls.recovery (fun _ ↦ some true))) :=
  ⟨BoundaryControls.differentRecovery_has_different_meaning.1⟩

/-- Any proof method is accepted when it proves the exact fixed meaning. -/
theorem direct_wrapper_receipt {claim : Claim} (proof : claim.Meaning) : Receipt claim := ⟨proof⟩

/-- An impossible premise can yield conditional evidence, but it does not prove the request. -/
theorem impossible_premise_conditional :
    ConditionalReceipt (.soundness (acceptsStatement 2)) False := ⟨False.elim⟩

theorem impossible_premise_not_closed : ¬ Receipt (.soundness (acceptsStatement 2)) :=
  fun receipt ↦ accepting_negative_refused receipt.proof

theorem discharged_premise_receipt : Receipt (.soundness (acceptsStatement 1)) :=
  (show ConditionalReceipt (.soundness (acceptsStatement 1)) True from
    ⟨fun _ ↦ accepting_gap_established⟩).close trivial

/-- A custom proposition remains custom even when it happens to be a canonical meaning. -/
theorem custom_same_proposition_stays_custom :
    Receipt (.custom (acceptsStatement 1).Holds) ∧
      ¬ (Claim.custom (acceptsStatement 1).Holds).IsCanonical :=
  ⟨⟨accepting_gap_established⟩, Claim.custom_not_canonical _⟩

@[expose] noncomputable def emptySoundness : SoundnessRequest Unit Nat Nat :=
  { acceptsStatement 2 with admissible := fun _ ↦ False }

theorem empty_admission_true_but_vacuous : emptySoundness.Holds ∧
    ¬ AdmitsInput emptySoundness.admissible := by
  have empty : ¬ AdmitsInput emptySoundness.admissible := by
    rintro ⟨_, impossible⟩
    exact impossible
  exact ⟨emptySoundness.toUpper.holds_of_empty empty, empty⟩

def populatedAdmission : AdmissionAssessment (acceptsStatement 1).admissible :=
  .inhabited () trivial

def emptyAdmission : AdmissionAssessment emptySoundness.admissible :=
  .empty empty_admission_true_but_vacuous.2

def informativeError : ErrorAssessment (acceptsStatement 1).admissible
    (acceptsStatement 1).error := .informative (by intro _ _; exact zero_lt_one)

def vacuousError : ErrorAssessment (fun _ : Unit ↦ True) (fun _ ↦ 1) :=
  .vacuous () trivial le_rfl

def finiteBudget : BudgetAssessment (fun _ : Unit ↦ True) (fun _ ↦ 1) :=
  .finite (by intro _ _; exact ENNReal.one_ne_top)

def unboundedBudget : BudgetAssessment (fun _ : Unit ↦ True) (fun _ ↦ ⊤) :=
  .unbounded () trivial rfl

end ProtocolProofExamples.ClaimBoundaries
