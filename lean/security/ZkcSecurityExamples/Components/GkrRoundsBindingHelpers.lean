module

public import ZkcSecurityExamples.Components.GkrRoundsGateRealization
public import ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation
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
open ZkcExamples.Structured.GkrSourceViews
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open GkrRoundsHelpers GkrRoundsRealization
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

noncomputable section
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem bodies : ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.Bodies payload.definitions := by
  bind_structured_bodies

theorem empty_body (args : Values (assignment F G) emptyHelper.inputs) :
    invoke table emptyHelper args =
      emptyBody.denote (Evaluation.meaning (.silent _) table) args.get := by
  rw [← generated_table]
  exact ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.empty_body (I := participantInterface F G) payload.linked bodies args

theorem append_body (args : Values (assignment F G) appendHelper.inputs) :
    invoke table appendHelper args =
      appendBody.denote (Evaluation.meaning (.silent _) table) args.get := by
  rw [← generated_table]
  exact ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.append_body (I := participantInterface F G) payload.linked bodies args

theorem empty : invoke (table (F := F) (G := G)) emptyHelper .nil =
    .done (.cons [] .nil) := by
  rw [← generated_table]
  exact ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.empty (I := participantInterface F G) payload.linked bodies

theorem append (point : List F) (r : F) :
    invoke (table (G := G)) appendHelper (.cons point (.cons r .nil)) =
      .done (.cons (point ++ [r]) .nil) := by
  rw [← generated_table]
  exact ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.append (I := participantInterface F G) payload.linked bodies point r

theorem owned_empty (self : Nat) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed emptyHelper) .nil =
      .done (.cons (some []) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.owned_empty payload.linked bodies self

theorem owned_append (self : Nat) (point : Option (List F)) (r : F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed appendHelper)
      (.cons point (.cons (some r) .nil)) =
      match point with
      | none => .halt .incomplete
      | some point => .done (.cons (some (point ++ [r])) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.owned_append payload.linked bodies self point r

/-- The complete linear Pending boundary retains both optional components. -/
theorem owned_rounds_open (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed roundsOpenHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete :=
  ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.owned_rounds_open payload.linked bodies self point claim

theorem owned_rounds_close (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed roundsCloseHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete :=
  ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.owned_rounds_close payload.linked bodies self point claim

theorem owned_layer_open (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed layerOpenHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete :=
  ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.owned_layer_open payload.linked bodies self point claim

theorem owned_pending (self : Nat) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) payload).toOn.closed pendingHelper)
      (.cons claim .nil) =
      match claim with
      | some claim => .done (.cons (some []) (.cons (some claim) .nil))
      | none => .halt .incomplete :=
  ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation.owned_pending payload.linked bodies self claim

end
end ZkcSecurity.Examples.Components.GkrRoundsBindingHelpers
