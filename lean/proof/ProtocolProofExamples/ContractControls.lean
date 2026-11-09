module

public import ProtocolProof.Claims.Assembly
public import ProtocolProof.Components.Adequacy
public import ProtocolProofExamples.ExecutionControls

/-! Complete stopped events close through both roots and both public adequacy directions. -/

public section
open PIR MeasureTheory ProtocolProof
open ProtocolProofExamples.ExecutionControls
open scoped ENNReal

namespace ProtocolProofExamples.ContractControls

@[expose] def stoppedEvent (reason : Stop) : Set (Execution Nat Nat Nat) :=
  {out | out.outcome = .stopped reason ∧ (out.state = 0 ∨ out.state = 1) ∧ out.events = []}

@[expose] def client (reason : Stop) : Unit → Process signature Nat := fun _ ↦ .halt reason

@[expose] noncomputable def potential (reason : Stop) (current : Nat × List Nat) : ENNReal :=
  (stoppedEvent reason).indicator 1 ⟨.stopped reason, current.1, current.2⟩

theorem whole_initial_budget (reason : Stop) :
    (∫⁻ current, potential reason current ∂system.initialWithEvents ()) = 1 := by
  change (∫⁻ current, potential reason current
    ∂initialLaw.map (fun state ↦ (state, ([] : List Nat)))) = 1
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [initialLaw, potential, stoppedEvent, lintegral_add_measure,
    lintegral_smul_measure, ENNReal.inv_two_add_inv_two]

@[expose] noncomputable def upperRequest (reason : Stop) :
    UpperRequest Unit (Execution Nat Nat Nat) where
  experiment := system.experiment (client reason)
  admissible _ := True
  event := stoppedEvent reason
  measurable_event := MeasurableSet.of_discrete
  bound _ := 1

@[expose] noncomputable def lowerRequest (reason : Stop) :
    LowerRequest Unit (Execution Nat Nat Nat) where
  experiment := system.experiment (client reason)
  admissible _ := True
  event := stoppedEvent reason
  measurable_event := MeasurableSet.of_discrete
  bound _ := 1

private noncomputable def upperEvidence (reason : Stop) :
    UpperEvidence (upperRequest reason) system system (client reason) (fun _ s t ↦ s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := opExpectation (I := signature) (system.accumulatedOperations ())
  local_bound _ _ _ _ := le_rfl
  model_event _ := stoppedEvent reason
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ related observed := related ▸ observed
  potential _ := potential reason
  mathematics _ _ := UpperBound.halt reason le_rfl
  budget _ _ := (whole_initial_budget reason).le

private noncomputable def lowerEvidence (reason : Stop) :
    LowerEvidence (lowerRequest reason) system system (client reason) (fun _ s t ↦ s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := opExpectation (I := signature) (system.accumulatedOperations ())
  local_bound _ _ _ _ := le_rfl
  model_event _ := stoppedEvent reason
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ related observed := related.symm ▸ observed
  potential _ := potential reason
  mathematics _ _ := LowerBound.halt reason le_rfl
  budget _ _ := (whole_initial_budget reason).ge

theorem stopped_upper_root (reason : Stop) : (upperRequest reason).Holds :=
  (upperEvidence reason).establish

theorem stopped_lower_root (reason : Stop) : (lowerRequest reason).Holds :=
  (lowerEvidence reason).establish

theorem stopped_event_by_upper_adequacy (reason : Stop) :
    (system.experiment (client reason)).run () (stoppedEvent reason) ≤ 1 :=
  UpperBound.closed_event_le system (client reason) () (fun _ _ ↦ le_rfl)
    (stoppedEvent reason) MeasurableSet.of_discrete (UpperBound.halt reason le_rfl)
    (whole_initial_budget reason).le

theorem stopped_event_by_lower_adequacy (reason : Stop) :
    1 ≤ (system.experiment (client reason)).run () (stoppedEvent reason) :=
  LowerBound.le_closed_event system (client reason) () (fun _ _ ↦ le_rfl)
    (stoppedEvent reason) MeasurableSet.of_discrete (LowerBound.halt reason le_rfl)
    (whole_initial_budget reason).ge

@[expose] def stopReward : Outcome Nat → (Nat × List Nat) → ENNReal
  | .returned _, _ => 0
  | .stopped _, _ => 1

@[expose] def returnReward : Outcome Nat → (Nat × List Nat) → ENNReal
  | .returned _, _ => 1
  | .stopped _, _ => 0

/-- Prefix and every returned continuation satisfy upper contracts, but the stopped reward
cannot be discarded when binding them. -/
theorem upper_bind_requires_stopped_obligation (spec : OperationSpec signature Nat Nat) :
    UpperBound spec (.halt .reject : Process signature Nat) (fun _ _ ↦ 0) (fun _ ↦ 0) ∧
    (∀ value, UpperBound spec (.done value) stopReward (fun _ ↦ 0)) ∧
    ¬ UpperBound spec ((.halt .reject : Process signature Nat).bind .done)
      stopReward (fun _ ↦ 0) := by
  refine ⟨UpperBound.halt _ le_rfl, fun value ↦ UpperBound.pure value le_rfl, ?_⟩
  intro h
  have impossible := h (0, [])
  exact (not_le_of_gt (by simp : (0 : ENNReal) < 1)) impossible

/-- The lower direction likewise needs the reverse stopped-branch comparison. -/
theorem lower_bind_requires_stopped_obligation (spec : OperationSpec signature Nat Nat) :
    LowerBound spec (.halt .reject : Process signature Nat) (fun _ _ ↦ 1) (fun _ ↦ 1) ∧
    (∀ value, LowerBound spec (.done value) returnReward (fun _ ↦ 1)) ∧
    ¬ LowerBound spec ((.halt .reject : Process signature Nat).bind .done)
      returnReward (fun _ ↦ 1) := by
  refine ⟨LowerBound.halt _ le_rfl, fun value ↦ LowerBound.pure value le_rfl, ?_⟩
  intro h
  have impossible := h (0, [])
  exact (not_le_of_gt (by simp : (0 : ENNReal) < 1)) impossible

end ProtocolProofExamples.ContractControls
