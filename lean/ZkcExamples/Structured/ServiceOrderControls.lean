module

public import ZkcExamples.Structured.ServiceOrder
public import ZkcExamples.Structured.ApplicationWrapper
public import Mathlib.Algebra.Field.Rat

import Mathlib.Tactic.NormNum

public section

/-! Independent stateful handlers for the admitted source processes. Scripted
values are typed replies, not a sender-value or randomness assumption. Counts
are indexed by the actual service handle, including aliased formal ports. -/
namespace ZkcExamples.Structured.ServiceOrderControls

set_option smartUnfolding false
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies

inductive Reply where
  | value (value : ℚ)
  | stop (reason : PIR.Stop)
  | mismatch
  deriving DecidableEq, Repr

inductive Event where
  | draw (site : String) (handle : Nat) (value : ℚ)
  | drawStop (site : String) (handle : Nat) (reason : PIR.Stop)
  | send (site : String) (peer : Nat) (value : ℚ)
  | receive (site : String) (peer : Nat) (value : ℚ)
  | receiveStop (site : String) (peer : Nat) (reason : PIR.Stop)
  deriving DecidableEq, Repr

structure ProviderState where
  replies : List Reply
  counts : List (Nat × Nat) := []
  consumed : Nat := 0
  site : String := ""
  deriving DecidableEq, Repr

@[expose] def countRequest (handle : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(handle, 1)]
  | (current, count) :: rest =>
      if handle == current then (current, count + 1) :: rest
      else (current, count) :: countRequest handle rest

@[expose] def scalarReply (returned : ℚ → Event) (stopped : PIR.Stop → Event)
    (state : ProviderState) : PIR.Execution ProviderState Event ℚ :=
  match state.replies with
  | [] => ⟨.stopped .incomplete, state, [stopped .incomplete]⟩
  | .mismatch :: _ => ⟨.stopped .refused, state, [stopped .refused]⟩
  | .stop reason :: rest =>
      ⟨.stopped reason, { state with replies := rest, consumed := state.consumed + 1 },
        [stopped reason]⟩
  | .value value :: rest =>
      ⟨.returned value, { state with replies := rest, consumed := state.consumed + 1 },
        [returned value]⟩

@[expose] def handler : PIR.Handler (observedInterface ℚ ℚ) ProviderState Event
  | .mark site, state => ⟨.returned (), { state with site }, []⟩
  | .action (.query site _ (.cons handle .nil)), state =>
      scalarReply (.draw site handle) (.drawStop site handle)
        { state with counts := countRequest handle state.counts }
  | .action (.send (ty := .field _) site peer value), state =>
      ⟨.returned (), state, [.send site peer value]⟩
  | .action (.receive (.field _) site peer), state =>
      scalarReply (.receive site peer) (.receiveStop site peer) state
  | .action _, state => ⟨.stopped .refused, state, []⟩

@[expose] def runVerifier (go : Bool) (first second : Nat) (replies : List Reply) :=
  (ServiceOrderViews.program.observed ℚ ℚ 1
    (ServiceOrder.inputs (some go) (some first) (some second))).run handler { replies }

@[expose] def runReceiver (replies : List Reply) :=
  (ServiceOrderViews.program.observed ℚ ℚ 0
    (ServiceOrder.inputs none none none)).run handler { replies }

/-- The alias is one provider handle with four requests, not two fresh services. -/
theorem same_owner_alias :
    runVerifier true 7 7 [.value 2, .value 3, .value 5, .value 7, .value 99] =
      ⟨.returned (.cons none (.cons (some 17) .nil)),
        ⟨[.value 99], [(7, 4)], 4, ""⟩,
        [.draw "s0" 7 2, .draw "apply_2_s3_s0" 7 3,
         .draw "apply_2_s3_s2" 7 5, .send "apply_2_s3_s5_0" 0 8,
         .draw "s6" 7 7]⟩ := by
  unfold runVerifier
  rw [ServiceOrder.observed_verifier]
  have child : (3 : ℚ) + 5 = 8 := by norm_num
  have total : (2 : ℚ) + (3 + 5) + 7 = 17 := by norm_num
  rw [← child, ← total]
  rfl

theorem distinct_handles :
    runVerifier true 7 9 [.value 2, .value 3, .value 5, .value 7, .value 99] =
      ⟨.returned (.cons none (.cons (some 17) .nil)),
        ⟨[.value 99], [(7, 3), (9, 1)], 4, ""⟩,
        [.draw "s0" 7 2, .draw "apply_2_s3_s0" 7 3,
         .draw "apply_2_s3_s2" 9 5, .send "apply_2_s3_s5_0" 0 8,
         .draw "s6" 7 7]⟩ := by
  unfold runVerifier
  rw [ServiceOrder.observed_verifier]
  have child : (3 : ℚ) + 5 = 8 := by norm_num
  have total : (2 : ℚ) + (3 + 5) + 7 = 17 := by norm_num
  rw [← child, ← total]
  rfl

theorem false_guard_keeps_first_draw :
    runVerifier false 7 9 [.value 2, .value 99] =
      ⟨.stopped .reject, ⟨[.value 99], [(7, 1)], 1, "s2"⟩, [.draw "s0" 7 2]⟩ := by
  unfold runVerifier
  rw [ServiceOrder.observed_verifier]
  rfl

/-- A valid stopping reply is consumed; the later scripted suffix is untouched. -/
theorem second_child_draw_stops_prefix :
    runVerifier true 7 9 [.value 2, .value 3, .stop .abort, .value 99] =
      ⟨.stopped .abort, ⟨[.value 99], [(7, 2), (9, 1)], 3, "apply_2_s3_s2"⟩,
        [.draw "s0" 7 2, .draw "apply_2_s3_s0" 7 3,
         .drawStop "apply_2_s3_s2" 9 .abort]⟩ := by
  unfold runVerifier
  rw [ServiceOrder.observed_verifier]
  rfl

theorem second_child_mismatch_unconsumed :
    runVerifier true 7 9 [.value 2, .value 3, .mismatch, .value 99] =
      ⟨.stopped .refused,
        ⟨[.mismatch, .value 99], [(7, 2), (9, 1)], 2, "apply_2_s3_s2"⟩,
        [.draw "s0" 7 2, .draw "apply_2_s3_s0" 7 3,
         .drawStop "apply_2_s3_s2" 9 .refused]⟩ := by
  unfold runVerifier
  rw [ServiceOrder.observed_verifier]
  rfl

/-- The receiver returns 19 even when the independently executed sender sends 8. -/
theorem independently_received_value :
    runReceiver [.value 19, .value 99] =
      ⟨.returned (.cons (some 19) (.cons none .nil)), ⟨[.value 99], [], 1, ""⟩,
        [.receive "apply_2_s3_s5_0" 1 19]⟩ := by
  unfold runReceiver
  rw [ServiceOrder.observed_receiver]
  rfl

theorem wrapper_receiver_retains_nested_site :
    (ApplicationWrapperViews.program.observed ℚ ℚ 0
      (ServiceOrder.inputs none none none)).run handler { replies := [.value 19, .value 99] } =
      ⟨.returned (.cons (some 19) (.cons none .nil)), ⟨[.value 99], [], 1, ""⟩,
        [.receive "apply_13_apply_2_s0_s3_s5_0" 1 19]⟩ := by
  rw [ApplicationWrapper.observed_receiver]
  rfl

end ZkcExamples.Structured.ServiceOrderControls
