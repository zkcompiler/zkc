import ZkcSecurity.Examples.Components.GkrRoundsGateRealization
import TestsSecurity.GkrRoundsReference
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace TestsSecurity.GkrRoundsRealization
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open ZkcSecurity.Examples.Components
open GkrRoundsHelpers GkrRoundsProcesses GkrRoundsReference GkrRoundsRealization GkrRoundsGateRealization
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

noncomputable section

/-- Nonconstant wiring and both nonconstant wire factors in the actual (x,y) order. -/
def raw : RawState ℚ := ⟨[1, 2, 3, 4], [2, 5, 7, 11], [2, 2, 6, 6], [2, 6, 2, 6]⟩

def wiringAdd : Table ℚ 2 := fun bits =>
  if bits 0 then (if bits 1 then 4 else 3) else (if bits 1 then 2 else 1)
def wiringMul : Table ℚ 2 := fun bits =>
  if bits 0 then (if bits 1 then 11 else 7) else (if bits 1 then 5 else 2)
def below : Table ℚ 1 := fun bits => if bits 0 then 6 else 2

theorem concrete_vectors : callerVectors 1 wiringAdd wiringMul below = raw := by
  simp [callerVectors, GkrRoundsLayout.encode, List.ofFn_succ, vertex, wiringAdd, wiringMul, below, raw]

theorem concrete_represents : Represents raw (GkrRoundsLayout.state wiringAdd wiringMul below below) := by
  rw [← concrete_vectors]
  exact concrete_caller 1 wiringAdd wiringMul below (by norm_num [indexLimit])

/-- The arbitrary-prefix gate is instantiated on this genuinely nonconstant
caller layout, across the phase transition after the first challenge. -/
example (challenge : ℚ) :
    Represents (raw.prefix 1 (Fin.cons challenge Fin.elim0))
      ((data ℚ).restrictPrefix 1 (GkrRoundsLayout.state wiringAdd wiringMul below below)
        (Fin.cons challenge Fin.elim0)) :=
  prefix_represents 1 raw _ concrete_represents (Fin.cons challenge Fin.elim0)

theorem first_message :
    invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper raw.values =
      .done (.cons 88 (.cons 264 (.cons 200 .nil))) := by
  change invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper
    (.cons [1, 2, 3, 4] (.cons [2, 5, 7, 11] (.cons [2, 2, 6, 6] (.cons [2, 6, 2, 6] .nil)))) = _
  rw [round_equation]
  norm_num [raw, RawState.values, round, split, Primitive.evaluate, primitiveOutcome,
    mapped, Evaluation.mapShape, Evaluation.mapShapeRemaining, indexLimit, Finite.admitThen,
    PIR.Process.bind, get_there, Values.get_cons, Values.get, Environment.push, valuesFormula, quadraticsFormula, Gate.value, Gate.quadratic,
    List.range_succ, List.sum_cons]

theorem first_state : raw.restrict 2 = (⟨[5, 6], [12, 17], [10, 10], [2, 6]⟩ : RawState ℚ) := by
  norm_num [RawState.restrict, raw, restrictValues]

theorem first_restriction :
    invoke (table (F := ℚ) (G := ℚ)) gateRestrictionHelper (raw.values.append (.cons 2 .nil)) =
      .done (.cons [5, 6] (.cons [12, 17] (.cons [10, 10] (.cons [2, 6] .nil)))) := by
  rw [fixGates_success raw _ concrete_represents.1 (by norm_num [indexLimit]) 2]
  rw [first_state]
  rfl

theorem second_message :
    invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper (raw.restrict 2).values =
      .done (.cons 300 (.cons 612 (.cons 204 .nil))) := by
  rw [first_state]
  change invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper (.cons [5, 6]
    (.cons [12, 17] (.cons [10, 10] (.cons [2, 6] .nil)))) = _
  rw [round_equation]
  norm_num [round, split, Primitive.evaluate, primitiveOutcome, mapped,
    Evaluation.mapShape, Evaluation.mapShapeRemaining, indexLimit, Finite.admitThen,
    PIR.Process.bind, get_there, Values.get_cons, Values.get, Environment.push, valuesFormula, quadraticsFormula, Gate.value, Gate.quadratic, List.range_succ]

theorem nonconstant_off_cube :
    (⟨88, 264, 200⟩ : Zkc.Protocols.AlgebraicRounds.Message ℚ).evaluate 2 = 1416 := by
  norm_num [Zkc.Protocols.AlgebraicRounds.Message.evaluate]

theorem two_round_terminal :
    raw.prefix 2 (Fin.cons 2 (Fin.cons 3 Fin.elim0)) =
      (⟨[8], [27], [10], [14]⟩ : RawState ℚ) := by
  norm_num [RawState.prefix, RawState.restrict, raw, restrictValues]

theorem two_round_execution :
    executeRestrictions (G := ℚ) 2 raw.values (Fin.cons 2 (Fin.cons 3 Fin.elim0)) =
      .done (⟨[8], [27], [10], [14]⟩ : RawState ℚ).values := by
  rw [prefix_execution 2 raw _ concrete_represents, two_round_terminal]

/-- Empty/odd splits remain refused in the actual helper. -/
theorem empty_refuses :
    invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper
      (.cons [] (.cons [1, 2] (.cons [1, 2] (.cons [1, 2] .nil)))) = .halt .refused := by
  rw [round_equation]
  rfl

theorem odd_fix_refuses :
    invoke (table (F := ℚ) (G := ℚ)) factorRestrictionHelper (.cons [1, 2, 3] (.cons 2 .nil)) =
      .halt .refused := by
  rw [fix_equation, fix_all]
  norm_num

/-- Every split is valid here; the actual map still refuses unequal shapes. -/
theorem unequal_maps_refuse :
    invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper
      (.cons [1, 2] (.cons [1, 2, 3, 4] (.cons [1, 2] (.cons [1, 2] .nil)))) =
      .halt .refused := by
  rw [round_equation]
  norm_num [round, split, Primitive.evaluate, primitiveOutcome, mapped,
    Evaluation.mapShape, Evaluation.mapShapeRemaining, indexLimit, Finite.admitThen, PIR.Process.bind, get_there, Values.get_cons, Values.get, Environment.push]

theorem even_once_is_insufficient :
    fix (F := ℚ) (G := ℚ) [0, 1, 2, 3, 4, 5] 2 = .done (.cons [6, 7, 8] .nil) ∧
    fix (F := ℚ) (G := ℚ) [6, 7, 8] 2 = .halt .refused := by
  constructor <;> rw [fix_all] <;> norm_num [indexLimit, restrictValues]

/-- Symbolic capacity control does not allocate a 2^64-entry test fixture. -/
theorem capacity_exhausts (low high : List ℚ) (large : ¬ low.length < indexLimit) :
    invoke (table (F := ℚ) (G := ℚ)) interpolationsHelper (.cons low (.cons high (.cons 2 .nil))) =
      .halt .exhausted := map_interpolate_exhausted low high 2 large

/-- Availability is checked by the real owned Local-call ABI before splitting. -/
theorem missing_local_input :
    Participant.owned (0 : Nat) 0
      (invoke (helpers (F := ℚ) (G := ℚ) payload).toOn.closed roundMessageHelper)
      (.cons (some []) (.cons (some [1, 2]) (.cons (some [1, 2]) (.cons none .nil)))) =
      .halt .incomplete := by
  rw [owned_round]
  rfl

theorem inactive_owner_skips :
    Participant.owned (1 : Nat) 0
      (invoke (helpers (F := ℚ) (G := ℚ) payload).toOn.closed gateRestrictionHelper)
      (.cons none (.cons none (.cons none (.cons none (.cons none .nil))))) =
      .done (Values.absent (assignment ℚ ℚ) gateRestrictionHelper.outputs) := by
  rw [owned_fixGates]
  rfl

/-- Retaining the old left factor's full table causes an actual shape refusal. -/
theorem stale_factor_refuses :
    invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper
      (.cons [5, 6] (.cons [12, 17] (.cons raw.left (.cons [2, 6] .nil)))) = .halt .refused := by
  rw [round_equation]
  norm_num [raw, round, split, Primitive.evaluate, primitiveOutcome, mapped,
    Evaluation.mapShape, Evaluation.mapShapeRemaining, indexLimit, Finite.admitThen, PIR.Process.bind, get_there, Values.get_cons, Values.get, Environment.push]

/-- Even a stale factor with the right shape changes the off-cube observation. -/
theorem stale_value_changes :
    Gate.value (5 : ℚ) 12 2 2 + Gate.value 6 17 2 6 ≠ 1416 := by
  norm_num [Gate.value]

/-- Three active factors are refused by the reference's own admissibility gate. -/
theorem degree_three_refuses : ¬ admissible TestsSecurity.GkrRoundsReference.cubicState :=
  TestsSecurity.GkrRoundsReference.cubic_refuses

theorem degree_three_off_cube :
    (message TestsSecurity.GkrRoundsReference.cubicState).evaluate 2 ≠
      total (restrict TestsSecurity.GkrRoundsReference.cubicState 2) :=
  TestsSecurity.GkrRoundsReference.cubic_off_cube

def cubicRaw : RawState ℚ := ⟨[0, 0], [0, 1], [0, 1], [0, 1]⟩

theorem cubic_decodes : Decodes cubicRaw TestsSecurity.GkrRoundsReference.cubicState := by
  have dz : ofList? 1 [0, 0] = some TestsSecurity.GkrRoundsReference.zero := by
    simpa [GkrRoundsLayout.encode, List.ofFn_succ, vertex,
      TestsSecurity.GkrRoundsReference.zero] using
      GkrRoundsLayout.decode_encode TestsSecurity.GkrRoundsReference.zero
  have db : ofList? 1 [0, 1] = some TestsSecurity.GkrRoundsReference.bit := by
    simpa [GkrRoundsLayout.encode, List.ofFn_succ, vertex,
      TestsSecurity.GkrRoundsReference.bit] using
      GkrRoundsLayout.decode_encode TestsSecurity.GkrRoundsReference.bit
  exact ⟨dz, db, db, db⟩

/-- Perfect power-of-two shapes do not establish the independent-factor gate. -/
theorem cubic_not_represented :
    ¬ Represents cubicRaw TestsSecurity.GkrRoundsReference.cubicState :=
  fun represented => degree_three_refuses represented.2.1

/-- The actual helper still returns a triple for this inadmissible cubic input.
It is the realization invariant, rather than a dynamic independence check,
that excludes interpreting this triple as the reference marginal. -/
theorem actual_cubic_message :
    invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper cubicRaw.values =
      .done (.cons 0 (.cons 1 (.cons 0 .nil))) := by
  change invoke (table (F := ℚ) (G := ℚ)) roundMessageHelper
    (.cons [0, 0] (.cons [0, 1] (.cons [0, 1] (.cons [0, 1] .nil)))) = _
  rw [round_equation]
  norm_num [round, split, Primitive.evaluate, primitiveOutcome, mapped,
    Evaluation.mapShape, Evaluation.mapShapeRemaining, indexLimit, Finite.admitThen,
    PIR.Process.bind, get_there, Values.get_cons, Values.get, Environment.push,
    valuesFormula, quadraticsFormula, Gate.value, Gate.quadratic, List.range_succ]

theorem actual_cubic_off_cube :
    (⟨0, 1, 0⟩ : Zkc.Protocols.AlgebraicRounds.Message ℚ).evaluate 2 ≠
      Gate.value 0 2 2 2 := by
  norm_num [Zkc.Protocols.AlgebraicRounds.Message.evaluate, Gate.value]

#print axioms GkrRoundsLayout.encode_replicate
#print axioms GkrRoundsLayout.encode_tile
#print axioms GkrRoundsLayout.admissible_state
#print axioms GkrRoundsHelpers.map_values_left
#print axioms GkrRoundsHelpers.map_values_right
#print axioms GkrRoundsHelpers.map_quadratics
#print axioms GkrRoundsProcesses.round_equation
#print axioms GkrRoundsProcesses.fix_all
#print axioms GkrRoundsRealization.round_success
#print axioms GkrRoundsRealization.fixGates_success
#print axioms GkrRoundsRealization.owned_round
#print axioms GkrRoundsRealization.owned_fixGates
#print axioms GkrRoundsGateRealization.concrete_caller
#print axioms GkrRoundsGateRealization.prefix_helper_realization
#print axioms GkrRoundsGateRealization.prefix_execution
#print axioms GkrRoundsGateRealization.prefix_separate_decodes
#print axioms GkrRoundsGateRealization.factor_degree
#print axioms GkrRoundsGateRealization.factor_evaluation
#print axioms GkrRoundsGateRealization.prefix_factor_degrees
#print axioms GkrRoundsGateRealization.arbitrary_message_degree
#print axioms first_message
#print axioms second_message
#print axioms first_restriction
#print axioms two_round_execution
#print axioms empty_refuses
#print axioms odd_fix_refuses
#print axioms unequal_maps_refuse
#print axioms even_once_is_insufficient
#print axioms capacity_exhausts
#print axioms missing_local_input
#print axioms inactive_owner_skips
#print axioms stale_factor_refuses
#print axioms stale_value_changes
#print axioms degree_three_refuses
#print axioms cubic_decodes
#print axioms cubic_not_represented
#print axioms actual_cubic_message
#print axioms actual_cubic_off_cube
end
end TestsSecurity.GkrRoundsRealization
