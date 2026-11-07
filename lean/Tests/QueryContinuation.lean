module

public import Zkc.Realization.QueryContinuation

@[expose] public section

/-! Saved parent coordinates and child answer ordinals are independently
preserved. Equal types do not authorize substituting one for another. -/
set_option autoImplicit false
namespace Tests.QueryContinuation
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization QueryContinuation

def frame : Frame := ⟨7, 3, 11, 5, [1]⟩
def saved (model : DomainModel) : model.Value (layout "continuation" 1).type :=
  (7, 3, 11, 5, 1, ())

theorem encoded (model : DomainModel) : Encodes "continuation" 1 frame (saved model) :=
  ⟨(1, ()), rfl, rfl⟩

/-- The checked append executes at any arena length and caller prefix. -/
theorem save (model : DomainModel)
    (prior : List (model.Value (layout "continuation" 1).type))
    (bounded : prior.length < indexLimit) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence (layout "continuation" 1).type, rfl, prior⟩,
       .data (.index 7), .data (.index 3), .data (.index 11), .data (.index 5), .data (.index 1)]
    Stored "continuation" 1 (prior ++ [saved model]) prior.length frame ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (RecordAppend.result model (layout "continuation" 1) rfl environment prior (saved model)))
        ((RecordAppend.spine (layout "continuation" 1) ⟨6, 0, [1, 2, 3, 4, 5]⟩).block model environment)) := by
  dsimp only
  exact (encoded model).save prior rfl rfl _ 0 [1, 2, 3, 4, 5] rfl rfl bounded

theorem stable (model : DomainModel) (other : List (model.Value (layout "continuation" 1).type)) :
    Stored "continuation" 1 ([saved model] ++ other) 0 frame :=
  (stored_append [] (encoded model)).transport (by simp)

/-- No field operand is needed on the exhausted path: packing never runs. -/
theorem full_arena (model : DomainModel)
    (prior : List (model.Value (layout "continuation" 1).type))
    (full : ¬ prior.length < indexLimit) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence (layout "continuation" 1).type, rfl, prior⟩]
    Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
      (.halt .exhausted)
      ((RecordAppend.spine (layout "continuation" 1) ⟨1, 0, [99]⟩).block model environment)) :=
  ⟨RecordAppend.exhausted model _ _ rfl _ prior rfl full⟩

theorem parent_swap_refused (model : DomainModel) :
    ¬ Stored "continuation" 1 [saved model] 0 {frame with outerInstance := 11, parentInstance := 3} := by
  intro swapped
  have same := (stored_append [] (encoded model)).unique swapped
  have coordinate := congrArg Frame.parentInstance same
  contradiction

theorem prior_answer_swap_refused (model : DomainModel) :
    ¬ Stored "continuation" 1 [saved model] 0 {frame with answers := [0]} := by
  intro swapped
  have same := (stored_append [] (encoded model)).unique swapped
  have answers := congrArg Frame.answers same
  contradiction

abbrev kinds : Bool → Type
  | false => Nat
  | true => Bool

def arenas : (kind : Bool) → List (kinds kind)
  | false => [19, 23]
  | true => [false]

def later : (kind : Bool) → List (kinds kind)
  | false => [19, 23, 29]
  | true => [false, true]

theorem earlier : AnswersRead arenas [1, 0] (.cons (ty := false) 23 (.cons (ty := true) false .nil)) :=
  .cons rfl (.cons rfl .nil)

theorem ordered_resume : AnswersRead later [1, 0, 2]
    (.cons (ty := false) 23 (.cons (ty := true) false (.cons (ty := false) 29 .nil))) := by
  have kept := earlier.transport (after := later) (by
    intro kind
    cases kind
    · exact ⟨[29], rfl⟩
    · exact ⟨[true], rfl⟩)
  exact kept.append (.cons rfl .nil)

theorem answer_swap_refused :
    ¬ AnswersRead arenas [0, 1] (.cons (ty := false) 23 (.cons (ty := false) 19 .nil)) := by
  intro swapped
  have correct : AnswersRead arenas [0, 1] (.cons (ty := false) 19 (.cons (ty := false) 23 .nil)) :=
    .cons rfl (.cons rfl .nil)
  have same := correct.unique swapped
  have first := congrArg (fun values ↦ values.get .here) same
  contradiction

example : (RecordAppend.recognizeAt 6
    (RecordAppend.instructions (layout "continuation" 1) ⟨6, 0, [1, 2, 3, 4, 5]⟩)).isSome = true := by decide +kernel

-- The record appended by the third instruction must be the one just packed.
example : (RecordAppend.recognizeAt 6
    [(RecordAppend.instructions (layout "continuation" 1) ⟨6, 0, [1, 2, 3, 4, 5]⟩)[0],
     (RecordAppend.instructions (layout "continuation" 1) ⟨6, 0, [1, 2, 3, 4, 5]⟩)[1],
     ⟨.execute (.sequenceAppend (layout "continuation" 1).type), [0, 6],
       [.data (.sequence (layout "continuation" 1).type)], []⟩]).isNone = true := by decide +kernel

#print axioms save
#print axioms full_arena
#print axioms stable
#print axioms QueryContinuation.Stored.load
#print axioms ordered_resume
#print axioms parent_swap_refused
#print axioms prior_answer_swap_refused
#print axioms answer_swap_refused
end Tests.QueryContinuation
