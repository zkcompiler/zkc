module

public import Zkc.Realization.QueryAnswerReads

@[expose] public section

set_option autoImplicit false
namespace Tests.QueryAnswerReads
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization QueryAnswerReads

-- Both kinds have the same output type and independent arena namespaces.
abbrev answerType (_ : Bool) : Ty := .index

def arenas (model : DomainModel) : (kind : Bool) → List (model.Value (answerType kind))
  | false => [23]
  | true => [71]

def environment (model : DomainModel) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence .index, rfl, [23]⟩,
   .data ⟨.sequence .index, rfl, [71]⟩, .data (.index 0)]

def placement : AnswerReads.Placement ([false, true].map answerType) :=
  .cons 0 2 (.cons 1 2 .nil)

def swapped : AnswerReads.Placement ([false, true].map answerType) :=
  .cons 1 2 (.cons 0 2 .nil)

theorem association (model : DomainModel) :
    ArenaOperands model answerType (arenas model) (environment model) placement [0, 0] :=
  .cons rfl rfl rfl (.cons rfl rfl rfl .nil)

theorem stored (model : DomainModel) :
    QueryContinuation.AnswersRead (arenas model) [0, 0]
      (.cons (ty := false) 23 (.cons (ty := true) 71 .nil)) :=
  .cons rfl (.cons rfl .nil)

/-- Any caller suffix can use the same saved-answer and physical-read laws. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (suffix : Domain.Environment model.toCarriers) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment model ++ suffix <+: frame)
      (.done (environment model ++ suffix ++
        AnswerReads.encoded (model := model)
          (.cons (ty := .index) 23 (.cons (ty := .index) 71 .nil))))
      (Domain.evaluate model program context placement.instructions
        (environment model ++ suffix))) :=
  ((association model).extended suffix).actual (stored model) program context

/-- A type-correct physical arena swap breaks the saved continuation's meaning. -/
theorem swapped_arenas_refused (model : DomainModel) :
    ¬ ArenaOperands model answerType (arenas model) (environment model) swapped [0, 0] := by
  intro wrong
  have physical : AnswerReads.Readback model (environment model) swapped
      (.cons (ty := Ty.index) 71 (.cons (ty := Ty.index) 23 .nil)) :=
    .cons [71] 0 rfl rfl rfl rfl (.cons [23] 0 rfl rfl rfl rfl .nil)
  have same := physical.unique (wrong.readback (stored model))
  have impossible : (71 : Nat) = 23 := congrArg (fun tuple ↦ tuple.get .here) same
  contradiction

#print axioms actual
#print axioms swapped_arenas_refused
end Tests.QueryAnswerReads
