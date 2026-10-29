module

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

structure RawState (F : Type) where
  add : List F
  mul : List F
  left : List F
  right : List F

def RawState.values (raw : RawState F) :
    Values (assignment F G) [vector, vector, vector, vector] :=
  .cons raw.add (.cons raw.mul (.cons raw.left (.cons raw.right .nil)))

def Decodes {n : Nat} (raw : RawState F) (s : State F n) : Prop :=
  ofList? n raw.add = some s.add ∧ ofList? n raw.mul = some s.mul ∧
  ofList? n raw.left = some s.left ∧ ofList? n raw.right = some s.right

def RawState.restrict (raw : RawState F) (r : F) : RawState F :=
  ⟨restrictValues raw.add r, restrictValues raw.mul r,
    restrictValues raw.left r, restrictValues raw.right r⟩

def RawState.prefix : (count : Nat) → RawState F → (Fin count → F) → RawState F
  | 0, raw, _ => raw
  | count + 1, raw, challenges =>
    RawState.prefix count (raw.restrict (challenges 0)) (challenges ∘ Fin.succ)

omit [DecidableEq F] in
theorem restriction_decodes {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (decoded : Decodes raw s) (r : F) : Decodes (raw.restrict r) (restrict s r) :=
  ⟨ofList?_restrictValues _ _ r decoded.1,
    ofList?_restrictValues _ _ r decoded.2.1,
    ofList?_restrictValues _ _ r decoded.2.2.1,
    ofList?_restrictValues _ _ r decoded.2.2.2⟩

omit [DecidableEq F] in
theorem prefix_decodes {n : Nat} (count : Nat) (raw : RawState F)
    (s : State F (n + count)) (decoded : Decodes raw s) (challenges : Fin count → F) :
    Decodes (raw.prefix count challenges) ((data F).restrictPrefix count s challenges) := by
  induction count generalizing raw with
  | zero => exact decoded
  | succ count ih =>
    exact ih _ _ (restriction_decodes raw s decoded (challenges 0)) (challenges ∘ Fin.succ)

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem split_success {n : Nat} (xs : List F) (s : Table F (n + 1))
    (decoded : ofList? (n + 1) xs = some s) :
    split (G := G) xs = .done (.cons (xs.take (xs.length / 2))
      (.cons (xs.drop (xs.length / 2)) .nil)) := by
  have shape := ofList?_length xs s decoded
  have even : xs.length > 0 ∧ xs.length % 2 = 0 := by
    rw [shape, Nat.pow_succ]
    constructor
    · positivity
    · omega
  simp only [split, Primitive.evaluate, even, and_self, ite_true, primitiveOutcome]

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

omit [DecidableEq F] in
/-- Flat sums are in the same MSB-first order as the mathematical Boolean sum. -/
theorem range_sum {n : Nat} (formula : Nat → F) (s : Table F n)
    (agree : ∀ i : Fin (2 ^ n), formula i = s (vertex n i)) :
    ((List.range (2 ^ n)).map formula).sum = booleanSum s := by
  have same : (List.range (2 ^ n)).map formula = GkrRoundsLayout.encode s := by
    apply List.ext_getElem
    · simp [GkrRoundsLayout.encode]
    · intro i h₁ h₂
      have bound : i < 2 ^ n := by simpa using h₁
      simpa [GkrRoundsLayout.encode] using agree ⟨i, bound⟩
  rw [same]
  exact (booleanSum_ofList? _ _ (GkrRoundsLayout.decode_encode s)).symm

omit [DecidableEq F] in
theorem values_sum {n : Nat} (a m l r : List F) (ta tm tl tr : Table F n)
    (da : ofList? n a = some ta) (dm : ofList? n m = some tm)
    (dl : ofList? n l = some tl) (dr : ofList? n r = some tr) :
    ((List.range (2 ^ n)).map (valuesFormula a m l r)).sum =
      booleanSum (fun bits => Gate.value (ta bits) (tm bits) (tl bits) (tr bits)) := by
  apply range_sum
  intro i
  simp only [valuesFormula, ofList?_entry a ta da i, ofList?_entry m tm dm i,
    ofList?_entry l tl dl i, ofList?_entry r tr dr i, Option.getD_some]

omit [DecidableEq F] in
theorem quadratics_sum {n : Nat} (a0 a1 m0 m1 l0 l1 r0 r1 : List F)
    (ta0 ta1 tm0 tm1 tl0 tl1 tr0 tr1 : Table F n)
    (da0 : ofList? n a0 = some ta0) (da1 : ofList? n a1 = some ta1)
    (dm0 : ofList? n m0 = some tm0) (dm1 : ofList? n m1 = some tm1)
    (dl0 : ofList? n l0 = some tl0) (dl1 : ofList? n l1 = some tl1)
    (dr0 : ofList? n r0 = some tr0) (dr1 : ofList? n r1 = some tr1) :
    ((List.range (2 ^ n)).map (quadraticsFormula a0 a1 m0 m1 l0 l1 r0 r1)).sum =
      booleanSum (fun bits => Gate.quadratic (ta0 bits) (ta1 bits) (tm0 bits) (tm1 bits)
        (tl0 bits) (tl1 bits) (tr0 bits) (tr1 bits)) := by
  apply range_sum
  intro i
  simp only [quadraticsFormula, ofList?_entry a0 ta0 da0 i, ofList?_entry a1 ta1 da1 i,
    ofList?_entry m0 tm0 dm0 i, ofList?_entry m1 tm1 dm1 i,
    ofList?_entry l0 tl0 dl0 i, ofList?_entry l1 tl1 dl1 i,
    ofList?_entry r0 tr0 dr0 i, ofList?_entry r1 tr1 dr1 i, Option.getD_some]

omit [DecidableEq F] in
theorem message_coefficients {n : Nat} (s : State F (n + 1)) :
    message s =
      ⟨booleanSum (fun bits => Gate.value (half s.add false bits) (half s.mul false bits)
          (half s.left false bits) (half s.right false bits)),
        booleanSum (fun bits => Gate.value (half s.add true bits) (half s.mul true bits)
          (half s.left true bits) (half s.right true bits)) -
        booleanSum (fun bits => Gate.value (half s.add false bits) (half s.mul false bits)
          (half s.left false bits) (half s.right false bits)) -
        booleanSum (fun bits => Gate.quadratic (half s.add false bits) (half s.add true bits)
          (half s.mul false bits) (half s.mul true bits) (half s.left false bits)
          (half s.left true bits) (half s.right false bits) (half s.right true bits)),
        booleanSum (fun bits => Gate.quadratic (half s.add false bits) (half s.add true bits)
          (half s.mul false bits) (half s.mul true bits) (half s.left false bits)
          (half s.left true bits) (half s.right false bits) (half s.right true bits))⟩ := by
  simp only [message, pointMessage, Gate.message, booleanSum_eq_sum, Finset.sum_sub_distrib]

theorem get_there {Value : Structured.Ty → Type} {types : List Structured.Ty} {head result : Structured.Ty}
    (value : Value head) (rest : Values Value types) (ref : Var types result) :
    (Values.cons value rest).get (.there ref) = rest.get ref := rfl

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
