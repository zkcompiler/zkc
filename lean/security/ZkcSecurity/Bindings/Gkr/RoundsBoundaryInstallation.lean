module

public import Zkc.Protocols.Gkr.Source.RoundHelpers
public import Zkc.Protocols.Sumcheck.Source.HelperLaws
public import Zkc.Source.Structured.ReferenceLaws
public import Zkc.Source.Structured.Participant

@[expose] public section

/-! Optional linear boundaries installed on any linked helper table. Exact body
associations cover the complete ABI; absence and inactive ownership retain their
ordinary participant semantics. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured.PrimitiveLibrary
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

structure Bodies (definitions : List CheckedDefinition) : Prop where
  empty : BodyIn definitions emptyHelper emptyBody
  append : BodyIn definitions appendHelper appendBody
  roundsOpen : BodyIn definitions roundsOpenHelper roundsOpenBody
  roundsClose : BodyIn definitions roundsCloseHelper roundsCloseBody
  layerOpen : BodyIn definitions layerOpenHelper layerOpenBody
  pending : BodyIn definitions pendingHelper pendingBody

noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] {I : PIR.Signature}
variable {definitions : List CheckedDefinition}
  (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions)
include linked bodies

/-- The closed half of the actual paired helper table, in any silent interface. -/
abbrev helpers (definitions : List CheckedDefinition) : HelperTable (assignment F G) I :=
  (definitions.foldl (Evaluation.ComponentTables.extend (.silent I)) ⟨[], []⟩).closed

theorem roundsOpen_body (args : Values (assignment F G) roundsOpenHelper.inputs) :
    invoke (helpers (I := I) definitions) roundsOpenHelper args =
      roundsOpenBody.denote (Evaluation.meaning (.silent I) (helpers definitions)) args.get := by
  obtain ⟨definition, member, signature, raw⟩ := bodies.roundsOpen
  simp only [helpers, Evaluation.ComponentTables.closed_fold]
  exact Evaluation.definitions_invoke_body_view_as (.silent I)
    definitions linked definition member roundsOpenHelper signature roundsOpenBody raw args

theorem roundsClose_body (args : Values (assignment F G) roundsCloseHelper.inputs) :
    invoke (helpers (I := I) definitions) roundsCloseHelper args =
      roundsCloseBody.denote (Evaluation.meaning (.silent I) (helpers definitions)) args.get := by
  obtain ⟨definition, member, signature, raw⟩ := bodies.roundsClose
  simp only [helpers, Evaluation.ComponentTables.closed_fold]
  exact Evaluation.definitions_invoke_body_view_as (.silent I)
    definitions linked definition member roundsCloseHelper signature roundsCloseBody raw args

theorem layerOpen_body (args : Values (assignment F G) layerOpenHelper.inputs) :
    invoke (helpers (I := I) definitions) layerOpenHelper args =
      layerOpenBody.denote (Evaluation.meaning (.silent I) (helpers definitions)) args.get := by
  obtain ⟨definition, member, signature, raw⟩ := bodies.layerOpen
  simp only [helpers, Evaluation.ComponentTables.closed_fold]
  exact Evaluation.definitions_invoke_body_view_as (.silent I)
    definitions linked definition member layerOpenHelper signature layerOpenBody raw args

theorem pending_body (args : Values (assignment F G) pendingHelper.inputs) :
    invoke (helpers (I := I) definitions) pendingHelper args =
      pendingBody.denote (Evaluation.meaning (.silent I) (helpers definitions)) args.get := by
  obtain ⟨definition, member, signature, raw⟩ := bodies.pending
  simp only [helpers, Evaluation.ComponentTables.closed_fold]
  exact Evaluation.definitions_invoke_body_view_as (.silent I)
    definitions linked definition member pendingHelper signature pendingBody raw args

theorem empty_body (args : Values (assignment F G) emptyHelper.inputs) :
    invoke (helpers (I := I) definitions) emptyHelper args =
      emptyBody.denote (Evaluation.meaning (.silent I) (helpers definitions)) args.get :=
by
  obtain ⟨definition, member, signature, raw⟩ := bodies.empty
  simp only [helpers, Evaluation.ComponentTables.closed_fold]
  exact Evaluation.definitions_invoke_body_view_as (.silent I)
    definitions linked definition member emptyHelper signature emptyBody raw args

theorem append_body (args : Values (assignment F G) appendHelper.inputs) :
    invoke (helpers (I := I) definitions) appendHelper args =
      appendBody.denote (Evaluation.meaning (.silent I) (helpers definitions)) args.get :=
by
  obtain ⟨definition, member, signature, raw⟩ := bodies.append
  simp only [helpers, Evaluation.ComponentTables.closed_fold]
  exact Evaluation.definitions_invoke_body_view_as (.silent I)
    definitions linked definition member appendHelper signature appendBody raw args

theorem empty : invoke (helpers (F := F) (G := G) (I := I) definitions) emptyHelper .nil =
    .done (.cons [] .nil) := by
  rw [empty_body linked bodies]
  rfl

theorem append (point : List F) (r : F) :
    invoke (helpers (G := G) (I := I) definitions) appendHelper (.cons point (.cons r .nil)) =
      .done (.cons (point ++ [r]) .nil) := by
  rw [append_body linked bodies]
  rfl

theorem owned_empty (self : Nat) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) (I := I) definitions) emptyHelper) .nil =
      .done (.cons (some []) .nil) := by
  simp only [Participant.owned, ite_true, RoleFamily.sequence, empty linked bodies, PIR.Process.bind]
  rfl

theorem owned_append (self : Nat) (point : Option (List F)) (r : F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) (I := I) definitions) appendHelper)
      (.cons point (.cons (some r) .nil)) =
      match point with
      | none => .halt .incomplete
      | some point => .done (.cons (some (point ++ [r])) .nil) := by
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    change (invoke (helpers (I := I) definitions) appendHelper (.cons point (.cons r .nil))).bind _ = _
    rw [append linked bodies]
    rfl

/-- The linear Pending boundaries retain both components and require both
inputs, including when the source repeat has zero iterations. -/
theorem owned_rounds_open (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) (I := I) definitions) roundsOpenHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete := by
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      change (invoke (helpers (I := I) definitions) roundsOpenHelper (.cons point (.cons claim .nil))).bind _ = _
      rw [roundsOpen_body linked bodies]
      rfl

theorem owned_rounds_close (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) (I := I) definitions) roundsCloseHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete := by
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      change (invoke (helpers (I := I) definitions) roundsCloseHelper (.cons point (.cons claim .nil))).bind _ = _
      rw [roundsClose_body linked bodies]
      rfl

theorem owned_layer_open (self : Nat) (point : Option (List F)) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) (I := I) definitions) layerOpenHelper)
      (.cons point (.cons claim .nil)) =
      match point, claim with
      | some point, some claim => .done (.cons (some point) (.cons (some claim) .nil))
      | _, _ => .halt .incomplete := by
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases point with
  | none => rfl
  | some point =>
    cases claim with
    | none => rfl
    | some claim =>
      change (invoke (helpers (I := I) definitions) layerOpenHelper (.cons point (.cons claim .nil))).bind _ = _
      rw [layerOpen_body linked bodies]
      rfl

theorem owned_pending (self : Nat) (claim : Option F) :
    Participant.owned self self
      (invoke (helpers (F := F) (G := G) (I := I) definitions) pendingHelper)
      (.cons claim .nil) =
      match claim with
      | some claim => .done (.cons (some []) (.cons (some claim) .nil))
      | none => .halt .incomplete := by
  rw [Participant.owned, ite_eq_left (Eq.refl self)]
  cases claim with
  | none => rfl
  | some claim =>
    change (invoke (helpers (I := I) definitions) pendingHelper (.cons claim .nil)).bind _ = _
    rw [pending_body linked bodies]
    rfl

end
end ZkcSecurity.Bindings.Gkr.RoundsBoundaryInstallation
