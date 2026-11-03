module

public import Zkc.Protocols.Sumcheck.Source.Library
public import Zkc.Source.Structured.NormalForm.Steps

@[expose] public section

/-! Representation laws for the installed linear Sumcheck claim. Names are
parameters of the checked helper signatures. A caller must supply exact body
membership in its admitted unit; these laws introduce no executable reference
input and do not assert that a pending claim is true. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.SumcheckPendingLaws
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open OriginalSumcheckLibrary SumcheckVerifierHelpers SumcheckPendingBodies

/-- Exact bodies of the claim constructor, consuming opener and successor constructor. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  pending : BodyIn definitions pendingHelper pendingBody
  openClaim : BodyIn definitions openClaimHelper openClaimBody
  atPrefix : BodyIn definitions atPrefixHelper atPrefixBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Closed custody erasure retains an explicit coordinate; it does not encode a message. -/
theorem pending_plain (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (scalar : F) :
    invoke (plainHelpers (F := F) (G := G) payload).closed pendingHelper (.cons scalar .nil) =
      .done (.cons 0 (.cons [] (.cons scalar .nil))) := by
  rw [closed_invoke_plain, bodies.pending.invoke payload.linked]
  rfl

/-- Opening consumes the supplied coordinate and preserves the mathematical fields. -/
theorem openClaim_plain (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (custody : CustodyToken) (point : List F) (scalar : F) :
    invoke (plainHelpers (F := F) (G := G) payload).closed openClaimHelper
      (.cons custody (.cons point (.cons scalar .nil))) =
      .done (.cons point (.cons scalar .nil)) := by
  rw [closed_invoke_plain, bodies.openClaim.invoke payload.linked]
  rfl

/-- Reconstructing a claim creates its successor coordinate in the closed interpretation. -/
theorem atPrefix_plain (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (point : List F) (scalar : F) :
    invoke (plainHelpers (F := F) (G := G) payload).closed atPrefixHelper
      (.cons point (.cons scalar .nil)) =
      .done (.cons 0 (.cons point (.cons scalar .nil))) := by
  rw [closed_invoke_plain, bodies.atPrefix.invoke payload.linked]
  rfl

theorem pending_closed (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (scalar : F) :
    invoke (helpers (F := F) (G := G) payload).closed pendingHelper (.cons scalar .nil) =
      .done (.cons 0 (.cons [] (.cons scalar .nil))) := by
  rw [← (helpers_lift payload).closed, pending_plain payload bodies scalar]
  rfl

theorem openClaim_closed (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (custody : CustodyToken) (point : List F) (scalar : F) :
    invoke (helpers (F := F) (G := G) payload).closed openClaimHelper (.cons custody (.cons point (.cons scalar .nil))) =
      .done (.cons point (.cons scalar .nil)) := by
  rw [← (helpers_lift payload).closed, openClaim_plain payload bodies custody point scalar]
  rfl

theorem atPrefix_closed (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (point : List F) (scalar : F) :
    invoke (helpers (F := F) (G := G) payload).closed atPrefixHelper (.cons point (.cons scalar .nil)) =
      .done (.cons 0 (.cons point (.cons scalar .nil))) := by
  rw [← (helpers_lift payload).closed, atPrefix_plain payload bodies point scalar]
  rfl

/-- Construction demands the scalar before any round admission, including zero rounds. -/
theorem pending_plain_owned (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self : Nat) (scalar : Option F) :
    Participant.owned (Value := assignment F G) self self
      (invoke (plainHelpers (F := F) (G := G) payload).closed pendingHelper)
      (.cons scalar .nil) =
      match scalar with
      | none => .halt .incomplete
      | some value => .done (.cons (some 0) (.cons (some []) (.cons (some value) .nil))) := by
  unfold Participant.owned
  rw [ite_eq_left rfl]
  cases scalar with
  | none => rfl
  | some value =>
    change (invoke (plainHelpers (F := F) (G := G) payload).closed pendingHelper
      (.cons value .nil)).bind _ = _
    rw [pending_plain payload bodies]
    rfl

theorem pending_owned (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self : Nat) (scalar : F) :
    Participant.owned (Value := assignment F G) self self
      (invoke (helpers (F := F) (G := G) payload).closed pendingHelper)
      (.cons (some scalar) .nil) =
      .done (.cons (some 0) (.cons (some []) (.cons (some scalar) .nil))) := by
  unfold Participant.owned
  rw [ite_eq_left rfl]
  change (invoke (helpers (F := F) (G := G) payload).closed pendingHelper
    (.cons scalar .nil)).bind _ = _
  rw [pending_closed payload bodies]
  rfl

/-- Every owned component, including custody, is demanded. Other roles stay absent. -/
theorem openClaim_owned (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self owner : Nat) (custody : Option CustodyToken)
    (point : Option (List F)) (scalar : Option F) :
    Participant.owned (Value := assignment F G) self owner
      (invoke (helpers (F := F) (G := G) payload).closed openClaimHelper)
      (.cons custody (.cons point (.cons scalar .nil))) =
      if owner = self then
        match custody, point, scalar with
        | some _, some p, some s => .done (.cons (some p) (.cons (some s) .nil))
        | _, _, _ => .halt .incomplete
      else .done (.cons none (.cons none .nil)) := by
  unfold Participant.owned
  by_cases same : owner = self
  · rw [ite_eq_left same, ite_eq_left same]
    cases custody with
    | none => cases point <;> cases scalar <;> rfl
    | some token =>
      cases point with
      | none => cases scalar <;> rfl
      | some p =>
        cases scalar with
        | none => rfl
        | some s =>
          change (invoke (helpers (F := F) (G := G) payload).closed openClaimHelper
            (.cons token (.cons p (.cons s .nil)))).bind _ = _
          rw [openClaim_closed payload bodies]
          rfl
  · rw [ite_eq_right same, ite_eq_right same]
    rfl

theorem atPrefix_owned (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self owner : Nat) (point : Option (List F)) (scalar : Option F) :
    Participant.owned (Value := assignment F G) self owner
      (invoke (helpers (F := F) (G := G) payload).closed atPrefixHelper)
      (.cons point (.cons scalar .nil)) =
      if owner = self then
        match point, scalar with
        | some p, some s => .done (.cons (some 0) (.cons (some p) (.cons (some s) .nil)))
        | _, _ => .halt .incomplete
      else .done (.cons none (.cons none (.cons none .nil))) := by
  unfold Participant.owned
  by_cases same : owner = self
  · rw [ite_eq_left same, ite_eq_left same]
    cases point with
    | none => cases scalar <;> rfl
    | some p =>
      cases scalar with
      | none => rfl
      | some s =>
        change (invoke (helpers (F := F) (G := G) payload).closed atPrefixHelper
          (.cons p (.cons s .nil))).bind _ = _
        rw [atPrefix_closed payload bodies]
        rfl
  · rw [ite_eq_right same, ite_eq_right same]
    rfl

/-- Data cannot repair an absent owned custody coordinate. -/
theorem openClaim_missing_custody (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self : Nat) (point : Option (List F)) (scalar : Option F) :
    Participant.owned (Value := assignment F G) self self
      (invoke (helpers (F := F) (G := G) payload).closed openClaimHelper)
      (.cons none (.cons point (.cons scalar .nil))) = .halt .incomplete := by
  rw [openClaim_owned payload bodies, ite_eq_left rfl]

end ZkcExamples.Structured.SumcheckPendingLaws
