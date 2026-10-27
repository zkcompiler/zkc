module

public import ZkcExamples.Structured.OriginalSumcheckLibrary
public import ZkcExamples.Structured.NormalFormSteps

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

abbrev claimTypes : List Ty := [.vector "bls12-381.fr", .field "bls12-381.fr"]

abbrev identityHelper (name : String) : Helper := ⟨name, .local, claimTypes, claimTypes⟩

def identityBody : Region dialect claimTypes claimTypes :=
  .ret (.cons .here (.cons (.there .here) .nil))

/-- Exact membership in the admitted helper table, including both consuming
wrappers and the caller constructor. No helper-correctness assumption escapes
an installed receipt: its generated installation discharges these fields. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  pending : BodyIn definitions pendingHelper pendingBody
  openClaim : BodyIn definitions openClaimHelper openClaimBody
  atPrefix : BodyIn definitions atPrefixHelper atPrefixBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The same representation law in the ordinary participant interface. -/
theorem identity_plain (payload : UnitPayload) (name : String)
    (body : BodyIn payload.definitions (identityHelper name) identityBody)
    (point : List F) (scalar : F) :
    invoke (plainHelpers (F := F) (G := G) payload).closed (identityHelper name)
      (.cons point (.cons scalar .nil)) = .done (.cons point (.cons scalar .nil)) := by
  rw [closed_invoke_plain, body.invoke payload.linked]
  rfl

/-- Constructing Pending consumes the scalar even when the requested round count is zero. -/
theorem pending_plain (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (scalar : F) :
    invoke (plainHelpers (F := F) (G := G) payload).closed pendingHelper (.cons scalar .nil) =
      .done (.cons [] (.cons scalar .nil)) := by
  rw [closed_invoke_plain, bodies.pending.invoke payload.linked]
  rfl

/-- Ordinary participant execution consumes the optional scalar at construction. -/
theorem pending_plain_owned (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self : Nat) (scalar : Option F) :
    Participant.owned (Value := assignment F G) self self
      (invoke (plainHelpers (F := F) (G := G) payload).closed pendingHelper)
      (.cons scalar .nil) =
      match scalar with
      | none => .halt .incomplete
      | some value => .done (.cons (some []) (.cons (some value) .nil)) := by
  unfold Participant.owned
  rw [ite_eq_left rfl]
  cases scalar with
  | none => rfl
  | some value =>
    change (invoke (plainHelpers (F := F) (G := G) payload).closed pendingHelper
      (.cons value .nil)).bind _ = _
    rw [pending_plain payload bodies]
    rfl

/-- Both opening a claim and constructing its successor preserve the complete
prefix and scalar. They are separate source helpers with separate body links. -/
theorem identity_closed (payload : UnitPayload) (name : String)
    (body : BodyIn payload.definitions (identityHelper name) identityBody)
    (point : List F) (scalar : F) :
    invoke (helpers (F := F) (G := G) payload).closed (identityHelper name)
      (.cons point (.cons scalar .nil)) = .done (.cons point (.cons scalar .nil)) := by
  rw [← (helpers_lift payload).closed, identity_plain payload name body]
  rfl

theorem pending_closed (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (scalar : F) :
    invoke (helpers (F := F) (G := G) payload).closed pendingHelper (.cons scalar .nil) =
      .done (.cons [] (.cons scalar .nil)) := by
  rw [← (helpers_lift payload).closed, pending_plain payload bodies]
  rfl

theorem pending_owned (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (self : Nat) (scalar : F) :
    Participant.owned (Value := assignment F G) self self
      (invoke (helpers (F := F) (G := G) payload).closed pendingHelper)
      (.cons (some scalar) .nil) = .done (.cons (some []) (.cons (some scalar) .nil)) := by
  unfold Participant.owned
  rw [ite_eq_left rfl]
  change (invoke (helpers (F := F) (G := G) payload).closed pendingHelper
    (.cons scalar .nil)).bind _ = _
  rw [pending_closed payload bodies]
  rfl

/-- Missing owned data stops as incomplete. Other roles skip the helper;
no missing readback is replaced by an arbitrary mathematical value. -/
theorem identity_owned (payload : UnitPayload) (name : String)
    (body : BodyIn payload.definitions (identityHelper name) identityBody)
    (self owner : Nat) (point : Option (List F)) (scalar : Option F) :
    Participant.owned (Value := assignment F G) (inputs := claimTypes) (outputs := claimTypes) self owner
      (invoke (helpers (F := F) (G := G) payload).closed (identityHelper name))
      (.cons point (.cons scalar .nil)) =
      if owner = self then
        match point, scalar with
        | some p, some s => .done (.cons (some p) (.cons (some s) .nil))
        | _, _ => .halt .incomplete
      else .done (.cons none (.cons none .nil)) := by
  unfold Participant.owned
  by_cases same : owner = self
  · rw [ite_eq_left same, ite_eq_left same]
    cases point with
    | none => cases scalar <;> rfl
    | some p =>
      cases scalar with
      | none => rfl
      | some s =>
        change (invoke (helpers (F := F) (G := G) payload).closed (identityHelper name)
          (.cons p (.cons s .nil))).bind _ = _
        rw [identity_closed payload name body p s]
        rfl
  · rw [ite_eq_right same, ite_eq_right same]
    rfl

/-- A partial verifier readback cannot be used as a complete pending claim. -/
theorem identity_owned_missing (payload : UnitPayload) (name : String)
    (body : BodyIn payload.definitions (identityHelper name) identityBody)
    (self : Nat) (point : Option (List F)) :
    Participant.owned (Value := assignment F G) self self
      (invoke (helpers (F := F) (G := G) payload).closed (identityHelper name))
      (.cons point (.cons none .nil)) = .halt .incomplete := by
  rw [identity_owned payload name body, ite_eq_left rfl]
  cases point <;> rfl

end ZkcExamples.Structured.SumcheckPendingLaws
