import Examples.OpeningReduction.Security
import Examples.OpeningReduction.Acceptance
import Examples.OpeningReduction.MultiplePoints
import Examples.OpeningReduction.Batching
import Mathlib.Data.ZMod.Basic

/-! Executable controls for the actual two-round source and opening consumer.

All equalities below are kernel-checked. Observing a returned bundle is distinct
from running a terminal verifier; the forged-value control exercises that gap.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Controls
open PIR
open Openings

abbrev F := ZMod 17

/-- The multilinear extension is `x + y`; the virtual product is its cube. -/
def table : Table F 2 := .node (.node (.scalar 0) (.scalar 1)) (.node (.scalar 1) (.scalar 2))
def product : Factors F 2 := ⟨table, table, table⟩
def objects : Objects Nat := ⟨10, 20, 30⟩
def environment (_ : Nat) : Table F 2 := table
def firstMessage : Message F := ⟨1, 3, 3, 2⟩

abbrev State := Nat × F

def send (state : State) : Message F × State :=
  (if state.1 = 0 then firstMessage else Message.product state.2 1 state.2 1 state.2 1,
    (state.1 + 1, state.2))

def react (state : State) (r : F) : State := (state.1, r)

def report (state : State) (acc : Source.Accumulator F) : Values F × State :=
  (⟨acc.challenges.sum, acc.challenges.sum, acc.challenges.sum⟩, (state.1 + 100, state.2))

def forged (state : State) (acc : Source.Accumulator F) : Values F × State :=
  (⟨1, 1, acc.claim⟩, (state.1 + 100, state.2))

def wrongProduct (state : State) (_ : Source.Accumulator F) : Values F × State :=
  (⟨0, 0, 0⟩, (state.1 + 100, state.2))

def observe {n : Nat} : Outcome (Bundle Nat F n) → Outcome (List (Nat × List F × F))
  | .returned claims => .returned (claims.map fun c => (c.object, List.ofFn c.point, c.value))
  | .stopped reason => .stopped reason

theorem actual_cubic_round : product.round = firstMessage := by decide
theorem actual_second_round : (product.restrict 2).round = ⟨8, 12, 6, 1⟩ := by decide
theorem actual_sum : product.booleanSum = 10 := by decide

theorem honest_obligations :
    observe (Openings.run send react report objects 2 10 (0, 0) [2, 3, 11]).outcome =
      .returned [(10, [2, 3], 5), (20, [2, 3], 5), (30, [2, 3], 5)] := by decide

theorem honest_state :
    (Openings.run send react report objects 2 10 (0, 0) [2, 3, 11]).state = ((102, 3), [11]) := by decide

theorem honest_events :
    (Openings.run send react report objects 2 10 (0, 0) [2, 3]).events =
      [.message firstMessage, .challenge 2, .message ⟨8, 12, 6, 1⟩, .challenge 3,
        .openingValues [5, 5, 5]] := by decide

theorem honest_terminal :
    accepted (valid environment) (Openings.run send react report objects 2 10 (0, 0) [2, 3]).outcome = true := by decide

/-- A failing first check neither consumes a challenge nor calls the reporter. -/
theorem boundary_failure :
    observe (Openings.run send react report objects 2 11 (0, 0) [2, 3]).outcome = .stopped .reject ∧
    (Openings.run send react report objects 2 11 (0, 0) [2, 3]).state = ((1, 0), [2, 3]) ∧
    (Openings.run send react report objects 2 11 (0, 0) [2, 3]).events =
      [.message firstMessage, .reject] := by decide

theorem exhaustion_preserves_message :
    observe (Openings.run send react report objects 2 10 (0, 0) [2]).outcome = .stopped .exhausted ∧
    (Openings.run send react report objects 2 10 (0, 0) [2]).state = ((2, 2), []) ∧
    (Openings.run send react report objects 2 10 (0, 0) [2]).events =
      [.message firstMessage, .challenge 2, .message ⟨8, 12, 6, 1⟩] := by decide

theorem product_failure_after_draws :
    observe (Openings.run send react wrongProduct objects 2 10 (0, 0) [2, 3, 11]).outcome = .stopped .reject ∧
    (Openings.run send react wrongProduct objects 2 10 (0, 0) [2, 3, 11]).state = ((102, 3), [11]) ∧
    (Openings.run send react wrongProduct objects 2 10 (0, 0) [2, 3, 11]).events =
      [.message firstMessage, .challenge 2, .message ⟨8, 12, 6, 1⟩, .challenge 3,
        .openingValues [0, 0, 0]] := by decide

theorem false_obligations_returned :
    observe (Openings.run send react forged objects 2 10 (0, 0) [2, 3]).outcome =
      .returned [(10, [2, 3], 1), (20, [2, 3], 1), (30, [2, 3], 6)] := by decide

theorem false_obligations_rejected_by_reference :
    accepted (valid environment) (Openings.run send react forged objects 2 10 (0, 0) [2, 3]).outcome = false := by decide

def deferredInput : Acceptance.Input Nat F State := ⟨objects, 2, 10, (0, 0), [2, 3]⟩
def forgedBundle : Bundle Nat F 2 :=
  bundle objects (Zkc.Polynomial.coordinates 2 [2, 3]) ⟨1, 1, 6⟩

/-- A satisfying witness realizes the false bundle faithfully; realization
soundness does not discharge its opening obligations. -/
theorem forged_constraints :
    Acceptance.constraints send react forged deferredInput forgedBundle ⟨6, [2, 3]⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem forged_bundle_false : ¬ AllHold environment forgedBundle := by
  rw [← valid_iff]
  decide

theorem forged_constraints_cannot_close :
    ¬ ∃ output acc, Acceptance.constraints send react forged deferredInput output acc ∧
      AllHold environment output := by
  intro closed
  obtain ⟨output, returned, holds⟩ :=
    (Acceptance.followed_by_openings send react forged deferredInput environment).mp closed
  have actual := (Acceptance.realization send react forged).sound
    deferredInput forgedBundle _ forged_constraints
  have same := Outcome.returned.inj (actual.symm.trans returned)
  exact forged_bundle_false (same.symm ▸ holds)

theorem false_obligations_counted_by_error_event :
    falseOpening environment (fun _ => true)
      (Openings.run send react forged objects 2 10 (0, 0) [2, 3]).outcome = true := by decide

theorem short_point_refused :
    observe (close objects (⟨1, [2]⟩ : Source.Accumulator F) ⟨1, 1, 1⟩ : Outcome (Bundle Nat F 2)) =
      .stopped .refused := by decide

theorem long_point_refused :
    observe (close objects (⟨1, [2, 3, 4]⟩ : Source.Accumulator F) ⟨1, 1, 1⟩ : Outcome (Bundle Nat F 2)) =
      .stopped .refused := by decide

/-- Identity and coordinate order affect truth even when arities agree. -/
def asymmetric (_ : Nat) : Table F 2 :=
  .node (.node (.scalar 0) (.scalar 2)) (.node (.scalar 1) (.scalar 3))

theorem coordinate_order_matters :
    valid asymmetric [⟨10, ![2, 3], 8⟩] = true ∧
    valid asymmetric [⟨10, ![3, 2], 8⟩] = false := by decide

def distinctObjects (id : Nat) : Table F 2 := if id = 10 then table else asymmetric id

theorem object_identity_matters :
    valid distinctObjects [⟨10, ![2, 3], 5⟩] = true ∧
    valid distinctObjects [⟨20, ![2, 3], 5⟩] = false := by decide

theorem dropping_obligation_hides_failure :
    valid environment [⟨10, ![2, 3], 5⟩, ⟨20, ![2, 3], 1⟩] = false ∧
    valid environment [⟨10, ![2, 3], 5⟩] = true := by decide

theorem multiple_point_identity :
    (MultiplePoints.reduction table 4 ![2, 3] ![5, 7]).booleanSum = 2 := by decide

theorem multiple_point_round_has_no_cubic_term :
    (MultiplePoints.reduction table 4 ![2, 3] ![5, 7]).round.cubic = 0 := by decide

/-- Flattening the Boolean product values preserves the initial sum but changes
the polynomial queried by the protocol away from the Boolean cube. -/
def collapsedProduct : Table F 2 :=
  .node (.node (.scalar 0) (.scalar 1)) (.node (.scalar 1) (.scalar 8))

theorem flattening_changes_residual :
    Zkc.Polynomial.cubeSum 2 collapsedProduct.eval = product.booleanSum ∧
    collapsedProduct.eval ![2, 3] ≠ product.eval ![2, 3] := by decide

end Examples.OpeningReduction.Controls
