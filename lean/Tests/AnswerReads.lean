module

public import Zkc.Realization.AnswerReads

@[expose] public section

set_option autoImplicit false
namespace Tests.AnswerReads
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization.AnswerReads

def frame (model : DomainModel) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence .index, rfl, [19, 23]⟩,
   .data ⟨.sequence .boolean, rfl, [false]⟩,
   .data (.index 1), .data (.index 0)]

def reads : Placement [.index, .boolean, .index] :=
  .cons 0 2 (.cons 1 3 (.cons 0 3 .nil))

theorem readback (model : DomainModel) :
    Readback model (frame model) reads (.cons 23 (.cons false (.cons 19 .nil))) :=
  .cons [19, 23] 1 rfl rfl rfl rfl
    (.cons [false] 0 rfl rfl rfl rfl
      (.cons [19, 23] 0 rfl rfl rfl rfl .nil))

/-- The same physical read rule works under any existing caller suffix, and
returns three ordered answers of two distinct types. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (suffix : Domain.Environment model.toCarriers) :
    Nonempty (Original.Simulation Eq (fun _ live ↦ frame model ++ suffix <+: live)
      (.done (frame model ++ suffix ++
        encoded (model := model) (.cons (ty := .index) 23
          (.cons (ty := .boolean) false (.cons (ty := .index) 19 .nil)))))
      (Domain.evaluate model program context reads.instructions (frame model ++ suffix))) :=
  ((readback model).extended suffix).actual program context

theorem swapped_answers_refused (model : DomainModel) :
    ¬ Readback model (frame model) reads (.cons 19 (.cons false (.cons 23 .nil))) := by
  intro swapped
  have same := (readback model).unique swapped
  have wrong : (23 : Nat) = 19 := congrArg (fun values ↦ values.get .here) same
  contradiction

/-- Missing first answer stops before an invalid second read. -/
theorem missing_before_bad_suffix (model : DomainModel) (program : Program) (context : Context) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence .index, rfl, ([] : List Nat)⟩, .data (.index 0)]
    Nonempty (Original.Simulation (Eq (α := Domain.Environment model.toCarriers))
      (fun _ live ↦ environment <+: live) (.halt .refused)
      (Domain.evaluate model program context
        (Placement.cons (type := .index) 0 1
          (.cons (type := .boolean) 99 100 .nil)).instructions environment)) :=
  missing model .index _ 0 1 [] 0 rfl rfl _ rfl rfl program context

example : (recognize reads.instructions).isSome = true := by decide +kernel

-- The result type is checked against the actual sequence element type.
example : (recognize [⟨.execute (.sequenceAt .index), [0, 2], [.data .boolean], []⟩]).isSome = false := by
  decide +kernel

#print axioms actual
#print axioms missing_before_bad_suffix
#print axioms swapped_answers_refused
end Tests.AnswerReads
