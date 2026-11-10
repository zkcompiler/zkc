module

public import Zkc.Tests.Verification.Construction.AssociationControls
public import Zkc.Tests.Verification.Construction.SharedServices

/-! Semantic counterexamples at actual admitted participants. These are kernel-checked
refutations, independent of whether a particular construction tactic finds a proof. -/

@[expose] public section
noncomputable section
open PIR Zkc.Source Zkc.Source.Structured ProtocolProof Std.WP
namespace ActualSourceConstruction.SemanticControls
open DrawPair (model specification State)

/-- Reversing same-typed actual arguments changes the asymmetric helper's result. -/
theorem swapped_arguments : ¬ UpperBound specification
    (Twice.actual.program.participantOn model 0
      (.cons (some 11) (.cons (some 7) .nil)))
    (fun outcome _ => match outcome with
      | .returned values => if values.get .here = some (-4) then 0 else 1
      | .stopped _ => 0)
    (fun _ => 0) := by
  change ¬ ∀ _ : State × List Nat, (1 : ENNReal) ≤ 0
  simp

/-- A stable caller and lookup key do not preserve a changed dependency's meaning. -/
theorem stale_dependency : ¬ UpperBound specification
    (AssociationControls.program.participantOn model 0
      (.cons (some 7) (.cons (some 11) .nil)))
    (fun outcome _ => match outcome with
      | .returned values => if values.get .here = some (-4) then 0 else 1
      | .stopped _ => 0)
    (fun _ => 0) := by
  change ¬ ∀ _ : State × List Nat, (1 : ENNReal) ≤ 0
  simp

/-- Same-typed service handles retain their association with ordered calls. -/
theorem swapped_handles : ¬ UpperBound specification
    (DrawPair.actual.program.participantOn model 0
      (.cons (some true) (.cons (some 2) (.cons (some 1) .nil))))
    (fun _ current => if current.2 = [1, 2] then 0 else 1)
    (fun _ => 0) := by
  intro bound
  let := DrawPair.lowerLogic
  have reached := DrawPair.participant_lower_law true 2 1
    (fun _ current => if current.2 = [1, 2] then (0 : ENNReal) else 1)
    (fun _ current => if current.2 = [1, 2] then (0 : ENNReal) else 1)
  have lower := (OperationSpec.lowerBound_iff_triple _ _ _ _ _ _).mpr reached
  have samePost : OperationSpec.outcomePost
      (fun (_ : Values (Component model.Value) DrawPair.drawPair.signature.outputs) (current : State × List Nat) =>
        if current.2 = [1, 2] then (0 : ENNReal) else 1)
      (fun _ current => if current.2 = [1, 2] then (0 : ENNReal) else 1) =
      (fun _ current => if current.2 = [1, 2] then (0 : ENNReal) else 1) := by
    funext outcome current
    cases outcome <;> rfl
  erw [samePost] at lower
  have impossible := (lower ((fun _ => 0), [])).trans (bound ((fun _ => 0), []))
  norm_num at impossible

/-- A premise that enables a branch cannot establish an always-returning claim without it. -/
theorem reached_stop : ¬ UpperBound specification
    (DrawPair.actual.program.participantOn model 0
      (.cons (some false) (.cons (some 1) (.cons (some 2) .nil))))
    (fun outcome _ => match outcome with
      | .returned _ => 0
      | .stopped _ => 1)
    (fun _ => 0) := by
  change ¬ ∀ _ : State × List Nat, (1 : ENNReal) ≤ 0
  simp

#print axioms swapped_arguments
#print axioms stale_dependency
#print axioms swapped_handles
#print axioms reached_stop
end ActualSourceConstruction.SemanticControls
