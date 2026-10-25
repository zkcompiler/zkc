module

public import Zkc.Construction.OriginalFold

@[expose] public section

/-! Compositional laws of the original construction fold. In particular repeat
uses the real source masking, captures, admission and reached iteration index.
No premise restricts the provider's replies or assumes successful execution.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A B : Type}

/-- A single original action expands through the shared nominal effect handler. -/
theorem fold_action (routing : Routing)
    (operation : (Structured.participantInterfaceOn carriers).Op) (state : State carriers) :
    fold routing (.call (.action operation) .done) state =
      operations routing (.action operation) state := by
  change (operations routing (.action operation) state).bind .done = _
  exact PIR.Process.bind_done _

theorem fold_enter (routing : Routing) (frame : Structured.Occurrence.Frame) (state : State carriers) :
    fold routing (.call (.enter frame) .done) state =
      .done ((), { state with frames := state.frames ++ [frame] }) := rfl

/-- Closing an exact frame restores the outer stack and retains the reached
history. The equation also applies when an inner loop has completed. -/
theorem fold_leave (routing : Routing) (frame : Structured.Occurrence.Frame)
    (frames : Frames) (history : Domain.History carriers) :
    fold routing (.call (.leave frame) .done) ⟨frames ++ [frame], history⟩ =
      .done ((), ⟨frames, history⟩) := by
  simp [fold, PIR.Process.interpretState, operations]

/-- This is the literal observed source repeat boundary, including mismatched
close refusal. A stopped body cannot reach its closing boundary. -/
theorem fold_within (routing : Routing) (site : String) (index : Nat)
    (body : PIR.Process (Structured.Occurrence.signature carriers) A) (state : State carriers) :
    fold routing (Structured.Occurrence.iterations.within site index body) state =
      (fold routing body { state with frames := state.frames ++ [⟨site, index⟩] }).bind
        (fun (value, final) =>
          if final.frames.getLast? = some ⟨site, index⟩ then
            .done (value, { final with frames := final.frames.dropLast })
          else .halt .refused) := by
  simp only [Structured.IterationObservations.within_eq, Structured.Occurrence.iterations,
    Structured.IterationObservations.enter, Structured.IterationObservations.leave,
    fold, PIR.Process.interpretState_bind, PIR.Process.interpretState, operations, PIR.Process.bind]
  congr 1
  funext result
  split <;> rfl

/-- Ordered source folds carry the actual prefix state to every next callback.
The target is an ordinary finite Process fold, not a second source evaluator. -/
theorem fold_finite (routing : Routing)
    (step : A → B → PIR.Process (Structured.Occurrence.signature carriers) A)
    (items : List B) (initial : A) (state : State carriers) :
    fold routing (Finite.fold step items initial) state =
      Finite.fold (fun (value, current) item => fold routing (step value item) current)
        items (initial, state) := by
  induction items generalizing initial state with
  | nil => rfl
  | cons item rest ih =>
    simp only [Finite.fold, fold_bind, ih]

/-- Source repeat admission precedes body construction, even for zero trips.
All optional state, captures, role masks and declared bounds remain explicit. -/
theorem fold_repeat (routing : Routing) (spec : Structured.RepeatSpec)
    (context : Structured.ProtocolContext) (self : Nat) (count : Option Nat)
    (initial : Values (Component carriers.Value) spec.state)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) (Structured.Occurrence.signature carriers)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (site : String) (state : State carriers) :
    fold routing (Structured.denoteRepeatOn spec context self count initial captures body
      Structured.Occurrence.iterations site) state =
      (if (spec.roles.map context.roles).contains self then
        match count with
        | none => .halt .incomplete
        | some count =>
          if count ≤ spec.maximum then
            Finite.fold (fun (value, current) index =>
              fold routing (Structured.Repeat.stepOn spec context self captures body value index
                Structured.Occurrence.iterations site) current)
              (List.range count)
              (Structured.maskValues self (context.mapScopes spec.stateScopes) initial, state)
          else .halt .refused
      else .done (Values.absent carriers.Value spec.state, state)) := by
  by_cases active : (spec.roles.map context.roles).contains self = true
  · simp only [Structured.denoteRepeatOn, active, ↓reduceIte]
    cases count with
    | none => rfl
    | some count =>
      simp only
      by_cases bound : count ≤ spec.maximum
      · simp only [bound, ↓reduceIte]
        exact fold_finite routing _ _ _ _
      · simp only [bound, ↓reduceIte]
        rfl
  · simp only [Structured.denoteRepeatOn, active]
    rfl

/-- A loop-state representation may change without changing interactions,
stops or reply-dependent control flow. This factors an actual callback fold
through its proved source state representation. -/
theorem finite_embed {I : PIR.Signature} {Small Large Item : Type}
    (embed : Small → Large) (left : Small → Item → PIR.Process I Small)
    (right : Large → Item → PIR.Process I Large)
    (law : ∀ value item, right (embed value) item =
      (left value item).bind (fun result => .done (embed result)))
    (items : List Item) (initial : Small) :
    Finite.fold right items (embed initial) =
      (Finite.fold left items initial).bind (fun result => .done (embed result)) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      simp only [Finite.fold, law, PIR.Process.bind_assoc, PIR.Process.bind, ih]

/-- An already-proved lawful source normalization can be folded without a
second evaluator. Each normalized operation is constructed at the reached
history and frame stack. -/
theorem fold_interpret {I : PIR.Signature} (routing : Routing)
    (translation : PIR.OperationInterpretation I (Structured.Occurrence.signature carriers))
    (source : PIR.Process I A) (state : State carriers) :
    fold routing (source.interpret translation) state =
      source.interpretState (fun operation current => fold routing (translation operation) current) state := by
  induction source generalizing state with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      simp only [PIR.Process.interpret, fold_bind, PIR.Process.interpretState]
      congr 1
      funext result
      exact ih result.1 result.2

/-- The ordinary participant actions of a lawful normalized source view have
exactly the same state-threaded construction as occurrence-wrapped actions. -/
theorem fold_actions (routing : Routing)
    (source : PIR.Process (Structured.participantInterfaceOn carriers) A) (state : State carriers) :
    fold routing (source.interpret Structured.Occurrence.actions) state =
      source.interpretState (fun operation current => operations routing (.action operation) current) state := by
  rw [fold_interpret]
  congr 1
  funext operation current
  exact fold_action routing operation current

/-- Body substitution is valid at every reached state and every typed reply.
This is suitable for one original Sumcheck round or a multi-call region. -/
theorem finite_congr (routing : Routing)
    (step : A → B → PIR.Process (Structured.Occurrence.signature carriers) A)
    (target : A × State carriers → B → PIR.Process (Domain.effects carriers) (A × State carriers))
    (law : ∀ value current item, fold routing (step value item) current = target (value, current) item)
    (items : List B) (initial : A) (state : State carriers) :
    fold routing (Finite.fold step items initial) state = Finite.fold target items (initial, state) := by
  rw [fold_finite]
  congr 1
  funext pair item
  exact law pair.1 pair.2 item

end Zkc.Construction.Original
