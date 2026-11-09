module

public import ProtocolProof.Claims.Transfer
public import ProtocolProof.Components.Installation

/-!
# Request-boundary counterexamples

These are proved refusals, not deliberately failing proof scripts. Every experiment has mass
one and every admissibility predicate has an inhabitant. The conclusions expose specific ways
of weakening a claim: accepting a false statement, losing honest acceptance, replacing a fixed
recovery algorithm, or giving a simulator the witness it is supposed to hide.
-/

public section

open MeasureTheory ProtocolProof
open scoped ENNReal

namespace ProtocolProofExamples.BoundaryControls

local instance : MeasurableSpace Bool := ⊤

@[expose] noncomputable def constantExperiment (output : Bool) : Experiment Unit Bool where
  run _ := Measure.dirac output
  normalized _ := inferInstance

/-- All executions accept a statement whose request-side meaning is false. -/
@[expose] noncomputable def acceptingFalse : SoundnessRequest Unit Bool Unit where
  experiment := constantExperiment true
  admissible _ := True
  accepts output := output = true
  statement _ := ()
  problem := PromiseProblem.ofPredicate (fun _ ↦ False)
  measurable_bad := MeasurableSet.of_discrete
  error _ := 0

/-- A bypass cannot establish a zero-error false-acceptance request. -/
theorem acceptingFalse_refused : ¬ acceptingFalse.Holds := by
  intro h
  have hbad := h () trivial
  simp [SoundnessRequest.toUpper, acceptingFalse,
    constantExperiment] at hbad

/-- The honest execution always rejects. -/
@[expose] noncomputable def rejectingHonest : CompletenessRequest Unit Bool where
  experiment := constantExperiment false
  admissible _ := True
  accepts := {true}
  measurable_accepts := MeasurableSet.of_discrete
  error _ := 0

/-- No returned correct value is not sufficient: the accepting mass must be one. -/
theorem rejectingHonest_refused : ¬ rejectingHonest.Holds := by
  intro h
  have hbad := h () trivial
  simp [CompletenessRequest.toLower, rejectingHonest,
    constantExperiment] at hbad

/-- A fixed recovery entry is part of the meaning, not chosen by its proof. -/
@[expose] noncomputable def recovery (recover : Bool → Option Bool) :
    RecoveryRequest Unit Bool Bool where
  experiment := constantExperiment true
  admissible _ := True
  requiresRecovery _ := True
  recover := recover
  validWitness _ witness := witness = true
  measurable_failure := MeasurableSet.of_discrete
  error _ := 0

/-- Returning the wrong witness fails even though a witness exists. -/
theorem wrongRecovery_refused : ¬ (recovery (fun _ ↦ some false)).toUpper.Holds := by
  intro h
  have hbad := h () trivial
  simp [recovery, RecoveryRequest.toUpper, constantExperiment] at hbad

/-- A witness-searching replacement proves a different request; it does not repair the fixed one. -/
theorem differentRecovery_has_different_meaning :
    (recovery (fun _ ↦ some true)).toUpper.Holds ∧
      ¬ (recovery (fun _ ↦ some false)).toUpper.Holds := by
  constructor
  · intro _ _
    simp [recovery, RecoveryRequest.toUpper, constantExperiment]
  · exact wrongRecovery_refused

/-- The real observation leaks the private witness; the fixed simulator sees only Unit. -/
@[expose] noncomputable def leakingView : ViewComparison Unit Bool Bool where
  real := { run := fun input ↦ Measure.dirac input.2, normalized := fun _ ↦ inferInstance }
  simulated := constantExperiment false
  valid _ _ := True
  error _ := 0

/-- Quantifying the simulator before the witness prevents a witness-dependent fake simulation. -/
theorem leakingView_refused : ¬ leakingView.Holds := by
  intro h
  have hbad := (h () true trivial {true} MeasurableSet.of_discrete).1
  simp [leakingView, constantExperiment] at hbad

/-- Admission is inhabited for all the controls, so the refusals do not rest on empty domains. -/
theorem controls_admit_environment :
    acceptingFalse.admissible () ∧ rejectingHonest.admissible () ∧
      (recovery (fun _ ↦ some false)).admissible () ∧ leakingView.valid () true := by
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- A zero measure cannot be passed off as a complete probability experiment. -/
theorem zero_law_not_normalized : ¬ IsProbabilityMeasure (0 : Measure Bool) := by
  intro h
  let := h
  have impossible : (0 : Measure Bool) Set.univ = 1 := measure_univ
  simp at impossible

/-- An empty state relation cannot cover nonzero initial laws. -/
theorem empty_initial_relation_refused :
    ¬ ExpectationWP.CouplingPost (Measure.dirac false) (Measure.dirac true)
      (fun _ _ ↦ False) := by
  intro h
  have impossible := Installation.coupling_event_le Set.univ ∅
    MeasurableSet.univ MeasurableSet.empty
    (h.mono fun _ _ hfalse ↦ False.elim hfalse)
  simp at impossible

end ProtocolProofExamples.BoundaryControls
