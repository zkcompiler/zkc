module

public import Zkc.Construction.OriginalABI
public import Zkc.Source.Structured.Linking

@[expose] public section
/-! The actual closed helper table supplies one reusable certificate for all
helper outcomes. A source equation or a successful helper result is not an
input to the rule. Lookup, complete ABI encoding and nominal sorts are checked.
-/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured

def HelperReturns {model : DomainModel} {types : List Ty}
    (encode : Values model.Value types → Domain.Environment model.toCarriers)
    (state : State model.toCarriers) (environment : Domain.Environment model.toCarriers)
    (source : Values model.Value types × State model.toCarriers)
    (final : Domain.Environment model.toCarriers) : Prop :=
  ∃ result, source = (result, state) ∧ final = environment ++ encode result

/-- The exact closure found in the existing compiled helper table is also the
source closure. Every stop, including exhaustion, is preserved structurally. -/
def Simulation.closedHelper (model : DomainModel) (program : Program) (routing : Routing)
    (entry : HelperDefinition model.Value closedInterface)
    (found : (Domain.helperTable model program).find?
      (fun candidate => candidate.helper.name == entry.helper.name) = some entry)
    (arguments : Values model.Value entry.helper.inputs)
    (encoded : Domain.Environment model.toCarriers)
    (inputEncoding : Domain.encodeValues arguments = some encoded)
    (encode : Values model.Value entry.helper.outputs → Domain.Environment model.toCarriers)
    (outputEncoding : ∀ result, Domain.encodeValues result = some (encode result))
    (outputSorts : ∀ result,
      Domain.sortsMatch (entry.helper.outputs.map ValueSort.data) (encode result) = true)
    (state : State model.toCarriers) (environment : Domain.Environment model.toCarriers)
    (references : List Nat) (read : Domain.read environment references = some encoded) :
    Simulation (HelperReturns encode state environment)
      (fun _ frame => frame = environment)
      (fold routing ((entry.invoke arguments).interpret
        (closedLift (I := Occurrence.signature model.toCarriers))) state)
      (Domain.View.helper model program entry.helper.name references
        (entry.helper.outputs.map ValueSort.data) environment) := by
  have compiled := Domain.Binding.callHelper_of_lookup model program entry found arguments
    encoded inputEncoding
  cases computed : entry.invoke arguments with
  | done result =>
    simp only [computed, Domain.closedOutcome, outputEncoding result] at compiled
    simp only [Domain.View.helper, read, compiled, Domain.View.append, outputSorts,
      ↓reduceIte, PIR.Process.interpret, fold, PIR.Process.interpretState]
    exact .done ⟨result, rfl, rfl⟩
  | halt reason =>
    simp only [computed, Domain.closedOutcome] at compiled
    simp only [Domain.View.helper, read, compiled, PIR.Process.interpret, fold,
      PIR.Process.interpretState]
    exact .halt reason
  | call operation _ => exact nomatch operation

/-- Linked membership selects the actual closure, including its captured
definition prefix. This uniform specialization needs no helper outcome law. -/
def Simulation.linkedHelper {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (program : Program) (routing : Routing)
    (helper : Helper) (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    (arguments : Values (assignment F G) helper.inputs)
    (encoded : Domain.Environment (uniformCarriers F G))
    (inputEncoding : Domain.encodeValues arguments = some encoded)
    (encode : Values (assignment F G) helper.outputs → Domain.Environment (uniformCarriers F G))
    (outputEncoding : ∀ result, Domain.encodeValues result = some (encode result))
    (outputSorts : ∀ result,
      Domain.sortsMatch (helper.outputs.map ValueSort.data) (encode result) = true)
    (state : State (uniformCarriers F G)) (environment : Domain.Environment (uniformCarriers F G))
    (references : List Nat) (read : Domain.read environment references = some encoded) :
    Simulation (HelperReturns encode state environment) (fun _ frame => frame = environment)
      (fold routing ((invoke (closedMeanings program.payload.definitions) helper arguments).interpret
        (closedLift (I := Occurrence.signature (uniformCarriers F G)))) state)
      (Domain.View.helper (ringModel F G) program helper.name references
        (helper.outputs.map ValueSort.data) environment) := by
  apply Classical.choice
  obtain ⟨entry, found, signature⟩ := Evaluation.linked_lookup (F := F) (G := G)
    SiteObservations.closed program.payload.linked helper present
  rw [← Domain.Binding.helperTable_ringModel] at found
  subst helper
  simp only [closedMeanings, ← Domain.Binding.helperTable_ringModel, invoke, found, ↓reduceDIte]
  exact ⟨Simulation.closedHelper (ringModel F G) program routing entry found arguments encoded
    inputEncoding encode outputEncoding outputSorts state environment references read⟩

end Zkc.Construction.Original
