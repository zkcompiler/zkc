module

public import Zkc.Construction.OriginalHelperEncoding
public import Zkc.Source.Structured.PlainHelpers
public import ZkcExamples.Structured.GkrSourceViews

@[expose] public section
/-! Closed helper instantiations use the admitted source's actual dependency
fold. Membership and complete nominal encodings are the only obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrOriginalHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem source (helper : Helper) (arguments : Values (assignment F G) helper.inputs) :
    (invoke (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      helper arguments).interpret Occurrence.actions =
    (invoke (closedMeanings GkrSourceViews.unit.definitions) helper arguments).interpret
      (closedLift (I := Occurrence.signature (uniformCarriers F G))) := by
  rw [Zkc.Source.Structured.closed_invoke_plain]
  cases invoke (closedMeanings (F := F) (G := G) GkrSourceViews.unit.definitions) helper arguments with
  | done => rfl
  | halt => rfl
  | call impossible _ => exact nomatch impossible

def certificate (routing : Original.Routing) (helper : Helper)
    (present : helper ∈ GkrSourceViews.program.payload.definitions.map CheckedDefinition.helper)
    (arguments : Values (assignment F G) helper.inputs)
    (encoded : Domain.Environment (uniformCarriers F G))
    (inputEncoding : Domain.encodeValues arguments = some encoded)
    (encode : Values (assignment F G) helper.outputs → Domain.Environment (uniformCarriers F G))
    (outputEncoding : ∀ result, Domain.encodeValues result = some (encode result))
    (outputSorts : ∀ result,
      Domain.sortsMatch (helper.outputs.map ValueSort.data) (encode result) = true)
    (state : Original.State (uniformCarriers F G)) (environment : Domain.Environment (uniformCarriers F G))
    (references : List Nat) (read : Domain.read environment references = some encoded) :
    Original.Simulation (Original.HelperReturns encode state environment) (fun _ frame => frame = environment)
      (Original.fold routing
        ((invoke (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
          helper arguments).interpret Occurrence.actions) state)
      (Domain.View.helper (ringModel F G) GkrSourceViews.program helper.name references
        (helper.outputs.map ValueSort.data) environment) := by
  rw [source]
  exact Original.Simulation.linkedHelper GkrSourceViews.program routing helper present arguments encoded
    inputEncoding encode outputEncoding outputSorts state environment references read

/-- Compose the actual captured closure without exposing its interpreter. The
continuation is checked for every complete nominal helper result. -/
def continuation {A B : Type} (routing : Original.Routing) (helper : Helper)
    (present : helper ∈ GkrSourceViews.program.payload.definitions.map CheckedDefinition.helper)
    (inputData : helper.inputs.all Domain.dataType = true)
    (outputData : helper.outputs.all Domain.dataType = true)
    (arguments : Values (assignment F G) helper.inputs)
    (state : Original.State (uniformCarriers F G))
    (environment : Domain.Environment (uniformCarriers F G)) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments)
    (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects (uniformCarriers F G)) A →
      Domain.Environment (uniformCarriers F G) → Prop)
    (sourceNext : (Values (assignment F G) helper.outputs × Original.State (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A)
    (targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B)
    (frames : ∀ process, live (PIR.Process.bind process sourceNext) environment)
    (tail : ∀ result, Original.Simulation returns live
      (sourceNext (result, state)) (targetNext (environment ++ Original.encodeHelperResult result))) :
    Original.Simulation returns live
      ((Original.fold routing
        ((invoke (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
          helper arguments).interpret Occurrence.actions) state).bind sourceNext)
      ((Domain.View.helper (ringModel F G) GkrSourceViews.program helper.name references
        (helper.outputs.map ValueSort.data) environment).bind targetNext) := by
  rw [source]
  apply (Original.Simulation.linkedDataHelper GkrSourceViews.program routing helper present outputData
    arguments environment references read state inputData).bind
  · intro process frame equal
    subst frame
    exact frames process
  · intro original final related
    apply Classical.choice
    obtain ⟨result, rfl, rfl⟩ := related
    exact ⟨tail result⟩

end ZkcExamples.Construction.GkrOriginalHelpers
