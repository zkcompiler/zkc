module

public import Zkc.Semantics.Execution
public import Std.WP

@[expose] public section

/-! Pointwise weakest preconditions for the actual deterministic runner.

The selected handler determines replies, state changes and events. Both return
and stop postconditions see the final state and the complete event prefix.
This interpretation supplies no probability or all-replies abstraction.
Install `wpMonad handler` locally: the program type does not select a handler.
-/

set_option autoImplicit false

namespace PIR.WeakestPrecondition
open Std.WP Lean.Order

variable {I : Signature} {S E A B : Type}

/-- Read the complete execution without identifying a return with a stop. -/
def satisfies (execution : Execution S E A) (post : A → S → List E → Prop)
    (stopped : Stop → S → List E → Prop) (preceding : List E) : Prop :=
  match execution.outcome with
  | .returned value => post value execution.state (preceding ++ execution.events)
  | .stopped reason => stopped reason execution.state (preceding ++ execution.events)

/-- The exact run, with an incoming observation prefix. The prefix is not
handler state and cannot change which reply the handler returns. -/
def runWP (handler : Handler I S E) (process : Process I A)
    (post : A → S → List E → Prop)
    (epost : EStack⟨Stop → S → List E → Prop⟩) (state : S) (preceding : List E) : Prop :=
  satisfies (process.run handler state) post epost.1 preceding

theorem runWP_mono (handler : Handler I S E) (process : Process I A) :
    (⟨runWP handler process⟩ :
      PredTrans (S → List E → Prop) EStack⟨Stop → S → List E → Prop⟩ A).monotone := by
  intro post post' epost epost' stopImplies returnImplies state preceding holds
  change runWP handler process post' epost' state preceding
  change runWP handler process post epost state preceding at holds
  unfold runWP satisfies at holds ⊢
  split at holds
  · rename_i value _
    exact returnImplies value _ _ holds
  · rename_i reason _
    exact stopImplies.1 reason _ _ holds

theorem runWP_bind (handler : Handler I S E) (process : Process I A)
    (next : A → Process I B) (post : B → S → List E → Prop)
    (epost : EStack⟨Stop → S → List E → Prop⟩) :
    runWP handler (process.bind next) post epost =
      runWP handler process (fun value => runWP handler (next value) post epost) epost := by
  funext state preceding
  simp only [runWP, run_bind]
  cases process.run handler state with
  | mk outcome final events =>
    cases outcome with
    | stopped reason => rfl
    | returned value =>
      simp only [Execution.follow, satisfies, runWP]
      cases (next value).run handler final with
      | mk outcome final tail =>
        cases outcome <;> simp only [List.append_assoc]

/-- A handler-specific interpretation, intended exclusively for local instances.
The Lean 4.35 field names are confined to this definition. -/
@[reducible] def wpMonad (handler : Handler I S E) :
    WPMonad (Process I) (S → List E → Prop) EStack⟨Stop → S → List E → Prop⟩ where
  toWP _ := { wpTrans := fun process => ⟨runWP handler process⟩,
              wp_trans_monotone := runWP_mono handler }
  pure_le_wp_pure value post epost := by
    intro state preceding holds
    change runWP handler (.done value) post epost state preceding
    simpa only [runWP, Process.run, satisfies, List.append_nil] using holds
  bind_le_wp_bind process next post epost := by
    intro state preceding holds
    change runWP handler (process.bind next) post epost state preceding
    rw [runWP_bind]
    exact holds

/-- Adequacy is equality with the exact run, including state, events and stops. -/
theorem wp_eq_run (handler : Handler I S E) (process : Process I A)
    (post : A → S → List E → Prop) (stopped : Stop → S → List E → Prop)
    (state : S) (preceding : List E) :
    (letI := wpMonad handler
     wp process post estack⟨stopped⟩ state preceding) =
      satisfies (process.run handler state) post stopped preceding := rfl

theorem triple_iff_run (handler : Handler I S E) (process : Process I A)
    (pre : S → List E → Prop) (post : A → S → List E → Prop)
    (stopped : Stop → S → List E → Prop) :
    (letI := wpMonad handler
     Triple process pre post estack⟨stopped⟩) ↔
      ∀ state preceding, pre state preceding →
        satisfies (process.run handler state) post stopped preceding := by
  letI := wpMonad handler
  constructor
  · rintro ⟨holds⟩
    exact holds
  · intro holds
    exact ⟨holds⟩

/-- With an impossible stop postcondition, adequacy requires an actual return.
No terminal reason, including rejection, can satisfy this triple. -/
theorem triple_iff_returned (handler : Handler I S E) (process : Process I A)
    (pre : S → List E → Prop) (post : A → S → List E → Prop) :
    (letI := wpMonad handler
     Triple process pre post estack⟨fun _ _ _ => False⟩) ↔
      ∀ state preceding, pre state preceding → ∃ value,
        (process.run handler state).outcome = .returned value ∧
        post value (process.run handler state).state
          (preceding ++ (process.run handler state).events) := by
  rw [triple_iff_run]
  constructor
  · intro holds state preceding before
    have after := holds state preceding before
    unfold satisfies at after
    split at after
    · rename_i value returned
      exact ⟨value, returned, after⟩
    · exact False.elim after
  · intro holds state preceding before
    obtain ⟨value, returned, after⟩ := holds state preceding before
    simp only [satisfies, returned]
    exact after

/-- One concrete handler step; stopped replies retain their state and events. -/
theorem call_spec (handler : Handler I S E) (operation : I.Op)
    (post : I.Reply operation → S → List E → Prop)
    (stopped : Stop → S → List E → Prop) :
    (letI := wpMonad handler
     Triple (Process.call operation .done)
       (fun state preceding => satisfies (handler operation state) post stopped preceding)
       post estack⟨stopped⟩) := by
  apply (triple_iff_run _ _ _ _ _).mpr
  intro state preceding holds
  simpa only [Process.run, Execution.follow_return] using holds

theorem halt_spec (handler : Handler I S E) (reason : Stop)
    (post : A → S → List E → Prop) (stopped : Stop → S → List E → Prop) :
    (letI := wpMonad handler
     Triple (Process.halt reason : Process I A) (stopped reason) post estack⟨stopped⟩) := by
  apply (triple_iff_run _ _ _ _ _).mpr
  intro state preceding holds
  simpa only [Process.run, satisfies, List.append_nil] using holds

end PIR.WeakestPrecondition
