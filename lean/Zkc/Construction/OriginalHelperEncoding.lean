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

theorem Domain.Value.encode_sort {ty : Ty} {input : carriers.Value ty}
    {encoded : Domain.Value carriers} (ok : Domain.Value.encode ty input = some encoded) :
    encoded.sort = .data ty := by
  unfold Domain.Value.encode Domain.Payload.ofValue at ok
  split at ok
  · simp only [Option.map_some, Option.some.injEq] at ok
    subst encoded
    rfl
  · simp at ok

theorem Domain.encodeValues_sorts {tys : List Ty}
    {input : Values carriers.Value tys} {encoded : Domain.Environment carriers}
    (ok : Domain.encodeValues input = some encoded) :
    encoded.map Domain.Value.sort = tys.map ValueSort.data := by
  induction input generalizing encoded with
  | nil => simp only [Domain.encodeValues, Option.some.injEq] at ok; subst encoded; rfl
  | cons head tail ih =>
    simp only [Domain.encodeValues] at ok
    cases hh : Domain.Value.encode _ head with
    | none => simp [hh] at ok
    | some value =>
      cases ht : Domain.encodeValues tail with
      | none => simp [hh, ht] at ok
      | some values =>
        simp [hh, ht] at ok
        subst encoded
        simp only [List.map_cons, Domain.Value.encode_sort hh, ih ht]

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
