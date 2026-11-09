module

public import Zkc.Program.Execution
public import Zkc.Program.Semantics.Yields

@[expose] public section

/-! Changing the presentation of a complete return value leaves the process
unchanged when encoding restores every value. Effects and stops are retained. -/

set_option autoImplicit false
namespace PIR.Process

/-- A reversible return view preserves the complete process, including every
reply continuation and stopped branch. Only the returned value is decoded. -/
theorem restore_return {I : Signature} {A B : Type}
    (encode : B → A) (decode : A → B)
    (roundtrip : ∀ value, encode (decode value) = value) (process : Process I A) :
    process = (process.bind fun value => .done (decode value)).bind
      (fun value => .done (encode value)) := by
  rw [bind_assoc]
  simp only [bind, roundtrip, bind_done]

/-- A return view need only restore reachable values. The premise covers every
reply continuation; stops and effects are retained by the complete equation. -/
theorem restore_return_of_yields {I : Signature} {A B : Type}
    (encode : B → A) (decode : A → B) (process : Process I A)
    (roundtrip : Yields (fun value ↦ encode (decode value) = value) process) :
    process = (process.bind fun value ↦ .done (decode value)).bind
      (fun value ↦ .done (encode value)) := by
  rw [bind_assoc]
  have same := roundtrip.bind_congr
    (first := fun value ↦ Process.done value)
    (second := fun value ↦ Process.done (encode (decode value)))
    (fun value restores ↦ congrArg Process.done restores.symm)
  simpa only [bind_done, bind] using same

/-- Reconstruct a complete process from an explicit projected equation and a
view that restores all reachable returns. Return-only facts cannot replace
the projected equation, which also retains every call and stopped branch. -/
theorem reconstruct_from_reachable_view {I : Signature} {A B : Type}
    (process : Process I A) (view : A → B) (pack : B → A)
    (roundtrip : Yields (fun value ↦ pack (view value) = value) process)
    (reference : Process I B)
    (projected : process.bind (fun value ↦ .done (view value)) = reference) :
    process = reference.bind (fun value ↦ .done (pack value)) := by
  rw [← projected]
  exact restore_return_of_yields pack view process roundtrip

end PIR.Process

namespace PIR.Execution

variable {S E A B : Type}

/-- Repacking a return preserves the terminal state, including after a stop. -/
theorem follow_return_state (result : Execution S E A) (pack : A → B) :
    (result.follow (fun value state ↦ ⟨.returned (pack value), state, []⟩)).state =
      result.state := by
  cases result with | mk outcome state events => cases outcome <;> rfl

/-- Repacking a return preserves the entire reached event prefix. -/
theorem follow_return_events (result : Execution S E A) (pack : A → B) :
    (result.follow (fun value state ↦ ⟨.returned (pack value), state, []⟩)).events =
      result.events := by
  cases result with | mk outcome state events => cases outcome <;> simp [follow]

/-- An injective return representation reflects every exact returned value;
stops cannot be mistaken for returns. -/
theorem follow_return_returned_iff (result : Execution S E A) (pack : A → B)
    (injective : Function.Injective pack) (value : A) :
    (result.follow (fun value state ↦ ⟨.returned (pack value), state, []⟩)).outcome =
      .returned (pack value) ↔ result.outcome = .returned value := by
  cases result with
  | mk outcome state events =>
    cases outcome <;> simp [follow, injective.eq_iff]

/-- Transport a returned-value observation through a complete execution.
The observation must identify the chosen value on every packed return. -/
theorem follow_return_observed_iff (result : Execution S E A) (pack : A → B)
    (predicate : B → Prop) (value : A)
    (identifies : ∀ returned, predicate (pack returned) ↔ returned = value) :
    (match (result.follow (fun value state ↦ ⟨.returned (pack value), state, []⟩)).outcome with
      | .returned returned => predicate returned
      | .stopped _ => False) ↔ result.outcome = .returned value := by
  cases result with
  | mk outcome state events => cases outcome <;> simp [follow, identifies]

end PIR.Execution

namespace PIR.Process

/-- Execute a return-only continuation using the existing full bind law. -/
theorem run_bind_return {I : Signature} {S E A B : Type}
    (process : Process I A) (pack : A → B) (handler : Handler I S E) (state : S) :
    (process.bind (fun value ↦ .done (pack value))).run handler state =
      (process.run handler state).follow
        (fun value current ↦ ⟨.returned (pack value), current, []⟩) :=
  run_bind handler process (fun value ↦ .done (pack value)) state

/-- A complete projected equation and reachable inverse transport execution
without a new executor or a successful-outcome restriction. -/
theorem run_of_reachable_view {I : Signature} {S E A B : Type}
    (process : Process I A) (view : A → B) (pack : B → A)
    (roundtrip : Yields (fun value ↦ pack (view value) = value) process)
    (reference : Process I B)
    (projected : process.bind (fun value ↦ .done (view value)) = reference)
    (handler : Handler I S E) (state : S) :
    process.run handler state = (reference.run handler state).follow
      (fun value current ↦ ⟨.returned (pack value), current, []⟩) := by
  rw [reconstruct_from_reachable_view process view pack roundtrip reference projected]
  exact run_bind_return reference pack handler state

/-- The global inverse specialization is useful for complete ABI tuples. -/
theorem run_of_return_view {I : Signature} {S E A B : Type}
    (process : Process I A) (view : A → B) (pack : B → A)
    (roundtrip : ∀ value, pack (view value) = value) (reference : Process I B)
    (projected : process.bind (fun value ↦ .done (view value)) = reference)
    (handler : Handler I S E) (state : S) :
    process.run handler state = (reference.run handler state).follow
      (fun value current ↦ ⟨.returned (pack value), current, []⟩) := by
  have reconstructed := restore_return pack view roundtrip process
  rw [projected] at reconstructed
  rw [reconstructed]
  exact run_bind_return reference pack handler state

end PIR.Process
