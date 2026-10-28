module

public import Zkc.Construction.OriginalHelpers

@[expose] public section
/-! Complete nominal helper result encodings follow from their declared data
sorts. The rule never assumes that the actual closure succeeds. -/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

namespace Original

def encodeHelperResult {tys : List Ty} (result : Values carriers.Value tys) :
    Domain.Environment carriers := (Domain.encodeValues result).getD []

theorem encodeHelperResult_eq {tys : List Ty} (data : tys.all Domain.dataType = true)
    (result : Values carriers.Value tys) :
    Domain.encodeValues result = some (encodeHelperResult result) :=
  Domain.encodeValues_getD result data

theorem encodeHelperResult_sorts {tys : List Ty} (data : tys.all Domain.dataType = true)
    (result : Values carriers.Value tys) :
    Domain.sortsMatch (tys.map ValueSort.data) (encodeHelperResult result) = true := by
  simp only [Domain.sortsMatch, Domain.encodeValues_sorts (encodeHelperResult_eq data result), beq_self_eq_true]

/-- Generic nominal helper connection. The checked helper types supply the
complete encoding on every outcome; no mathematical result law is required. -/
def Simulation.linkedDataHelperOn (model : DomainModel) (program : Program) (routing : Routing)
    (helper : Helper) (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    (data : helper.outputs.all Domain.dataType = true)
    (arguments : Values model.Value helper.inputs)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments)
    (state : State model.toCarriers) (inputData : helper.inputs.all Domain.dataType = true) :
    Simulation (HelperReturns encodeHelperResult state environment) (fun _ frame => frame = environment)
      (fold routing ((invoke (Domain.helperTable model program) helper arguments).interpret
        (closedLift (I := Occurrence.signature model.toCarriers))) state)
      (Domain.View.helper model program helper.name references
        (helper.outputs.map ValueSort.data) environment) :=
  Simulation.linkedHelperOn model program routing helper present arguments (encodeHelperResult arguments)
    (encodeHelperResult_eq inputData arguments) encodeHelperResult
    (encodeHelperResult_eq data) (encodeHelperResult_sorts data) state environment references
    (read.trans (encodeHelperResult_eq inputData arguments))

def Simulation.linkedDataHelper {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (program : Program) (routing : Routing)
    (helper : Helper) (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    (data : helper.outputs.all Domain.dataType = true)
    (arguments : Values (assignment F G) helper.inputs)
    (environment : Domain.Environment (uniformCarriers F G))
    (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments)
    (state : State (uniformCarriers F G))
    (inputData : helper.inputs.all Domain.dataType = true) :
    Simulation (HelperReturns encodeHelperResult state environment) (fun _ frame => frame = environment)
      (fold routing ((invoke (closedMeanings program.payload.definitions) helper arguments).interpret
        (closedLift (I := Occurrence.signature (uniformCarriers F G)))) state)
      (Domain.View.helper (ringModel F G) program helper.name references
        (helper.outputs.map ValueSort.data) environment) :=
  Simulation.linkedHelper program routing helper present arguments (encodeHelperResult arguments)
    (encodeHelperResult_eq inputData arguments) encodeHelperResult
    (encodeHelperResult_eq data) (encodeHelperResult_sorts data) state environment references
    (read.trans (encodeHelperResult_eq inputData arguments))

end Original
end Zkc.Construction
