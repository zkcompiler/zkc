module

public import ZkcSecurity.Examples.Components.GkrRoundsGateRealization
public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Full-body laws for the two local helpers actually executed by role 1.
The existing round-message/factor-restriction realization remains shared. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBindingHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open GkrRoundsHelpers GkrRoundsRealization
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

noncomputable section
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem empty_body (args : Values (assignment F G) emptyHelper.inputs) :
    invoke table emptyHelper args =
      emptyBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.empty_closed args

theorem append_body (args : Values (assignment F G) appendHelper.inputs) :
    invoke table appendHelper args =
      appendBody.denote (Evaluation.meaning (.silent _) table) args.get :=
  ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.append_closed args

theorem empty : invoke (table (F := F) (G := G)) emptyHelper .nil =
    .done (.cons [] .nil) := by
  rw [empty_body]
  rfl

theorem append (point : List F) (r : F) :
    invoke (table (G := G)) appendHelper (.cons point (.cons r .nil)) =
      .done (.cons (point ++ [r]) .nil) := by
  rw [append_body]
  rfl

theorem owned_empty (self : Nat) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed emptyHelper) .nil =
      .done (.cons (some []) .nil) := by
  change Participant.owned self self (invoke (helpers payload).closed emptyHelper) .nil = _
  rw [generated_table]
  simp only [Participant.owned, ite_true, RoleFamily.sequence, empty, PIR.Process.bind]
  rfl

theorem owned_append (self : Nat) (point : Option (List F)) (r : F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed appendHelper)
      (.cons point (.cons (some r) .nil)) =
      match point with
      | none => .halt .incomplete
      | some point => .done (.cons (some (point ++ [r])) .nil) := by
  change Participant.owned self self (invoke (helpers payload).closed appendHelper) _ = _
  rw [generated_table]
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    change (invoke table appendHelper (.cons point (.cons r .nil))).bind _ = _
    rw [append]
    rfl

/-- The linear Pending boundaries retain both components and require both
inputs, including when the source repeat has zero iterations. -/
theorem owned_rounds_open (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed roundsOpenHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete := by
  change Participant.owned self self (invoke (helpers payload).closed roundsOpenHelper) _ = _
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      change (invoke (helpers payload).closed roundsOpenHelper (.cons point (.cons claim .nil))).bind _ = _
      rw [ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.roundsOpen_closed]
      rfl

theorem owned_rounds_close (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed roundsCloseHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete := by
  change Participant.owned self self (invoke (helpers payload).closed roundsCloseHelper) _ = _
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      change (invoke (helpers payload).closed roundsCloseHelper (.cons point (.cons claim .nil))).bind _ = _
      rw [ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.roundsClose_closed]
      rfl

theorem owned_layer_open (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed layerOpenHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete := by
  change Participant.owned self self (invoke (helpers payload).closed layerOpenHelper) _ = _
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      change (invoke (helpers payload).closed layerOpenHelper (.cons point (.cons claim .nil))).bind _ = _
      rw [ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.layerOpen_closed]
      rfl

theorem owned_pending (self : Nat) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed pendingHelper)
      (.cons claim .nil) =
      match claim with
      | some claim => .done (.cons (some []) (.cons (some claim) .nil))
      | none => .halt .incomplete := by
  change Participant.owned self self (invoke (helpers payload).closed pendingHelper) _ = _
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases claim with
  | none => rfl
  | some claim =>
    change (invoke (helpers payload).closed pendingHelper (.cons claim .nil)).bind _ = _
    rw [ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate.pending_closed]
    rfl

end
end ZkcSecurity.Examples.Components.GkrRoundsBindingHelpers
