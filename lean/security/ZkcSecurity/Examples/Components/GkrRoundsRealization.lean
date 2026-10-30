module

public import ZkcSecurity.Bindings.Gkr.RoundsRealization
public import ZkcSecurity.Examples.Components.GkrRoundsProcesses
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! The exact four-vector representation realizes the degree-two gate reference.
The equations concern complete Processes, including their stopping branches.
Every restriction updates all four factors separately. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsRealization
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.GkrSourceViews
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open GkrRoundsHelpers GkrRoundsProcesses GkrRoundsReference
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem fix_success {n : Nat} (xs : List F) (s : Table F (n + 1))
    (decoded : ofList? (n + 1) xs = some s) (capacity : 2 ^ n < indexLimit) (r : F) :
    fix (G := G) xs r = .done (.cons (restrictValues xs r) .nil) := by
  have shape : xs.length = 2 * 2 ^ n := by
    rw [ofList?_length xs s decoded, Nat.pow_succ, Nat.mul_comm]
  obtain ⟨low, high⟩ := restrictValues_halves_length xs shape
  rw [fix, split_success xs s decoded]
  simp only [PIR.Process.bind, Values.get]
  change invoke table interpolationsHelper
    (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) (.cons r .nil))) = _
  exact map_interpolate _ _ r (by omega) (by omega)

theorem fixGates_success {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (decoded : Decodes raw s) (capacity : 2 ^ n < indexLimit) (r : F) :
    invoke (table (G := G)) gateRestrictionHelper (raw.values.append (.cons r .nil)) =
      .done (raw.restrict r).values := by
  change invoke table gateRestrictionHelper (.cons raw.add (.cons raw.mul (.cons raw.left (.cons raw.right (.cons r .nil))))) = _
  rw [fixGates_equation]
  simp only [fixGates, fix_success _ _ decoded.1 capacity,
    fix_success _ _ decoded.2.1 capacity, fix_success _ _ decoded.2.2.1 capacity,
    fix_success _ _ decoded.2.2.2 capacity, PIR.Process.bind, Values.get, RawState.restrict, RawState.values]

theorem round_success {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (decoded : Decodes raw s) (capacity : 2 ^ n < indexLimit) :
    invoke (table (G := G)) roundMessageHelper raw.values =
      .done (.cons (message s).constant (.cons (message s).linear (.cons (message s).quadratic .nil))) := by
  have da0 := decode_low_half raw.add s.add decoded.1
  have da1 := decode_high_half raw.add s.add decoded.1
  have dm0 := decode_low_half raw.mul s.mul decoded.2.1
  have dm1 := decode_high_half raw.mul s.mul decoded.2.1
  have dl0 := decode_low_half raw.left s.left decoded.2.2.1
  have dl1 := decode_high_half raw.left s.left decoded.2.2.1
  have dr0 := decode_low_half raw.right s.right decoded.2.2.2
  have dr1 := decode_high_half raw.right s.right decoded.2.2.2
  change invoke table roundMessageHelper (.cons raw.add (.cons raw.mul (.cons raw.left (.cons raw.right .nil)))) = _
  rw [round_equation]
  unfold round
  rw [split_success _ _ decoded.1, split_success _ _ decoded.2.1,
    split_success _ _ decoded.2.2.1, split_success _ _ decoded.2.2.2]
  simp only [PIR.Process.bind, get_there, Values.get]
  simp only [ofList?_length _ _ da0, ofList?_length _ _ da1,
    ofList?_length _ _ dm0, ofList?_length _ _ dm1,
    ofList?_length _ _ dl0, ofList?_length _ _ dl1,
    ofList?_length _ _ dr0, ofList?_length _ _ dr1,
    mapped, Evaluation.mapShape, Evaluation.mapShapeRemaining, capacity, ite_true,
    Finite.admitThen, PIR.Process.bind, Values.get]
  rw [values_sum _ _ _ _ _ _ _ _ da0 dm0 dl0 dr0,
    values_sum _ _ _ _ _ _ _ _ da1 dm1 dl1 dr1,
    quadratics_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ da0 da1 dm0 dm1 dl0 dl1 dr0 dr1,
    message_coefficients]

/-- The exact all-present helper table in the generated Rounds binding. -/
theorem generated_table : (helpers (F := F) (G := G) payload).closed = table :=
  Evaluation.ComponentTables.closed_fold (.silent _) _ _

/-- This is the actual local-call seam of both generated participant views.
Every absent input is incomplete; an inactive owner skips the call. -/
theorem owned_round (self owner : Nat)
    (args : Values (Component (assignment F G)) roundMessageHelper.inputs) :
    Participant.owned self owner
      (invoke (helpers (F := F) (G := G) payload).toOn.closed roundMessageHelper) args =
    if owner = self then
      match RoleFamily.sequence args with
      | none => .halt .incomplete
      | some values => (round (values.get .here) (values.get (.there .here))
          (values.get (.there (.there .here)))
          (values.get (.there (.there (.there .here))))).bind fun out => .done out.present
    else .done (Values.absent (assignment F G) roundMessageHelper.outputs) := by
  unfold Participant.owned
  split
  · cases sequenced : RoleFamily.sequence args with
    | none => rfl
    | some values =>
      cases values with
      | cons a rest => cases rest with
        | cons m rest => cases rest with
          | cons l rest => cases rest with
            | cons r rest => cases rest
                             change (invoke (helpers payload).closed roundMessageHelper _).bind _ = _
                             rw [generated_table, round_equation]
                             rfl
  · rfl

theorem owned_fixGates (self owner : Nat)
    (args : Values (Component (assignment F G)) gateRestrictionHelper.inputs) :
    Participant.owned self owner
      (invoke (helpers (F := F) (G := G) payload).toOn.closed gateRestrictionHelper) args =
    if owner = self then
      match RoleFamily.sequence args with
      | none => .halt .incomplete
      | some values => (fixGates (values.get .here) (values.get (.there .here))
          (values.get (.there (.there .here))) (values.get (.there (.there (.there .here))))
          (values.get (.there (.there (.there (.there .here)))))).bind fun out => .done out.present
    else .done (Values.absent (assignment F G) gateRestrictionHelper.outputs) := by
  unfold Participant.owned
  split
  · cases sequenced : RoleFamily.sequence args with
    | none => rfl
    | some values =>
      cases values with
      | cons a rest => cases rest with
        | cons m rest => cases rest with
          | cons l rest => cases rest with
            | cons r rest => cases rest with
              | cons challenge rest => cases rest
                                       change (invoke (helpers payload).closed gateRestrictionHelper _).bind _ = _
                                       rw [generated_table, fixGates_equation]
                                       rfl
  · rfl

end
end ZkcSecurity.Examples.Components.GkrRoundsRealization
