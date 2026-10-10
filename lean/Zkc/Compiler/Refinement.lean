import Zkc.Compiler.Lowering
import Zkc.Realization.Simulation

/-! Source-to-plan refinement under actual interpretation and observation models.

Different languages, input contexts, values and final states can be related.
Model-specific operation laws are supplied by concrete proofs; they are not
inferred from operation names or required for every possible interpretation.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

/-- The logical execution selected by a consumer, separate from its native backend. -/
structure ExecutionModel (language : Language) where
  interface : PIR.Signature
  meaning : Interpretation language interface
  State : Type
  Event : Type
  handler : PIR.Handler interface State Event

variable {sourceLanguage targetLanguage : Language}

def ExecutionModel.runSource (model : ExecutionModel sourceLanguage) {Γ ty}
    (program : Program sourceLanguage Γ ty) (env : Environment model.meaning.Value Γ)
    (state : model.State) : PIR.Execution model.State model.Event (model.meaning.Value ty) :=
  (program.denote model.meaning env).run model.handler state

def ExecutionModel.runPlan (model : ExecutionModel targetLanguage) {Γ ty}
    (plan : Plan targetLanguage Γ ty) (env : Environment model.meaning.Value Γ)
    (state : model.State) : PIR.Execution model.State model.Event (model.meaning.Value ty) :=
  plan.run model.meaning model.handler env state

/-- The initial premise and final relation belong to the same consumed subject.
Returned values are interpreted in the actual final states, not the initial ones. -/
structure Refinement (source : ExecutionModel sourceLanguage)
    (target : ExecutionModel targetLanguage)
    (Γ : List sourceLanguage.Ty) (Δ : List targetLanguage.Ty)
    (result : sourceLanguage.Ty) (output : targetLanguage.Ty) where
  initial : Environment source.meaning.Value Γ → source.State →
    Environment target.meaning.Value Δ → target.State → Prop
  states : source.State → target.State → Prop
  values : source.meaning.Value result → source.State →
    target.meaning.Value output → target.State → Prop
  Observation : Type
  sourceView : source.Event → List Observation
  targetView : target.Event → List Observation

variable {source : ExecutionModel sourceLanguage} {target : ExecutionModel targetLanguage}
  {Γ : List sourceLanguage.Ty} {Δ : List targetLanguage.Ty}
  {result : sourceLanguage.Ty} {output : targetLanguage.Ty}

def Refinement.Holds (relation : Refinement source target Γ Δ result output)
    (program : Program sourceLanguage Γ result) (plan : Plan targetLanguage Δ output) : Prop :=
  ∀ sourceEnv sourceState targetEnv targetState,
    relation.initial sourceEnv sourceState targetEnv targetState →
    PIR.Execution.Relates relation.states relation.values relation.sourceView relation.targetView
      (source.runSource program sourceEnv sourceState) (target.runPlan plan targetEnv targetState)

/-- Exact logical execution is one refinement policy, not the only policy. -/
def Refinement.exact {language : Language} (model : ExecutionModel language)
    (Γ : List language.Ty) (ty : language.Ty) : Refinement model model Γ Γ ty ty where
  initial left s right t := @Eq (Environment model.meaning.Value Γ) left right ∧ s = t
  states := Eq
  values left _ right _ := left = right
  Observation := model.Event
  sourceView event := [event]
  targetView event := [event]

theorem Refinement.exact_of_execution {language : Language}
    (model : ExecutionModel language) {Γ ty} (program : Program language Γ ty)
    (plan : Plan language Γ ty)
    (law : ∀ env state, model.runSource program env state = model.runPlan plan env state) :
    (Refinement.exact model Γ ty).Holds program plan := by
  intro left s right t initial
  have sameInput : model.runSource program left s = model.runSource program right s :=
    congrArg (fun env : Environment model.meaning.Value Γ => model.runSource program env s) initial.1
  have sameState : model.runPlan plan right s = model.runPlan plan right t :=
    congrArg (fun state => model.runPlan plan right state) initial.2
  apply PIR.Execution.Relates.of_related
  rw [sameInput, law, sameState]
  exact ⟨rfl, rfl, rfl⟩

theorem Refinement.direct {language : Language} (model : ExecutionModel language)
    {Γ ty} (program : Program language Γ ty) :
    (Refinement.exact model Γ ty).Holds program (lower program) := by
  apply exact_of_execution
  intro env state
  exact (lower_correct model.meaning model.handler program env state).symm

end Zkc.Compiler
