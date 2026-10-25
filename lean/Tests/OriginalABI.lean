import Zkc.Construction.OriginalCorrespondence
import Mathlib.Data.ZMod.Basic

/-! Full input layout and nominal-identity controls. Values stay symbolic;
these are equations and laws, not enumerations of provider executions. -/
set_option autoImplicit false
noncomputable section
namespace Tests.OriginalABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Construction.Original

private def model : DomainModel := ringModel (ZMod 5) (ZMod 5)
private def types : List Ty := [.field "F", .boolean, .service "random.F/0"]
private def abi : InputABI :=
  ⟨[.data (.field "F"), .transcript "suite"], [.data 0, .absent, .capability 73]⟩
private def frame (field : String) (value : ZMod 5) : Domain.Environment model.toCarriers :=
  [.data (.field field value), .transcript "suite" []]
private def sourceInputs (value : ZMod 5) : Values (Component model.Value) types :=
  .cons (some value) (.cons none (.cons (some 73) .nil))

example (value : ZMod 5) : abi.read (frame "F" value) types = some (sourceInputs value) := rfl
example (value : ZMod 5) : ValuesHolds (frame "F" value) abi.locations (sourceInputs value) :=
  (abi.read_iff _ _ _).mp rfl |>.2

-- Different nominal fields remain distinct despite equal host carriers.
example (value : ZMod 5) : abi.read (frame "G" value) types = none := rfl
example (value : ZMod 5) :
    readComponents (frame "G" value) [.field "F"] [.data 0] = none := rfl
-- A malformed input cannot become an optional absent component.
example (value : ZMod 5) : readComponents (frame "F" value) [.field "F"] [.data 99] = none := rfl
example (value : ZMod 5) :
    readComponents (frame "F" value) [.field "F"] [.absent] = some (.cons none .nil) := rfl
example (value : ZMod 5) : abi.read (frame "F" value ++ [.indices []]) types = none := rfl
-- Layouts account for every slot, and capabilities cannot stand for data.
example (value : ZMod 5) : readComponents (frame "F" value) types [] = none := rfl
example (value : ZMod 5) :
    readComponents (frame "F" value) [.field "F"] [.capability 73] = none := rfl

-- Distinct owner-local services have their own nominal effect and never change
-- the construction history or frames, for every request-indexed provider reply.
example {carriers : Carriers} (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) (port : ServicePort) (origin : Origin)
    (mode : routing.mode = .producer)
    (route : routing.local state.frames site field handle = some (port, origin))
    (request : origin.request = some (.draw field)) :
    query routing state site field handle =
      .call (.localService port origin) (fun reply =>
        .done (fieldReply origin field request reply, state)) :=
  private_query_producer routing state site field handle port origin mode route request

#print axioms Zkc.Construction.Original.Simulation.source_run
#print axioms Zkc.Construction.Original.readComponents_iff
#print axioms Zkc.Construction.Original.Simulation.malformedABI
#print axioms Zkc.Construction.Original.RegionDerivation.sound
#print axioms Zkc.Construction.Original.Simulation.iterate
#print axioms Zkc.Construction.Original.fold_within_actions
#print axioms Zkc.Construction.Original.Simulation.original_source
end Tests.OriginalABI
