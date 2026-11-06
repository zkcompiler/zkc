module

public import Tests.IndexServicesExecution

@[expose] public section

/-! Actual local capability handlers remain separate from public queries.
The explicit counter control charges 100 for a private service and 1 for a
public service, without asserting any honest distribution or native receipt. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Tests.IndexServices.Private
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def replies (carriers : Carriers) : Domain.LocalServices Id carriers Nat :=
  fun _ _ origin state =>
    if scalar : origin.request = some (.sampleIndex 3) then
      (.returned (by simpa only [Domain.Raw, scalar] using
        (show Request.Raw carriers (.sampleIndex 3) from ⟨1, by decide⟩)), state + 100)
    else if block : origin.request = some (.sampleIndices 3 2) then
      (.returned (by simpa only [Domain.Raw, block] using
        (show Request.Raw carriers (.sampleIndices 3 2) from
          fun _ : Fin 2 => (⟨1, by decide⟩ : Fin 3))), state + 100)
    else (.stopped .refused, state + 100)

def producer (model : DomainModel) := Domain.produce model Local.program Local.context
  Local.Producer.participant [.transcript suite []] (Execution.fixedOracle model.toCarriers) 0
  (replies model.toCarriers)
def validator (model : DomainModel) := Domain.validate model Local.program Local.context
  Local.Validator.participant [.transcript suite []] [] (Execution.fixedOracle model.toCarriers) 0
  (replies model.toCarriers)

example (model : DomainModel) : (producer model).state.oracle = 201 := by kernel_rfl
example (model : DomainModel) : (validator model).state.oracle = 101 := by kernel_rfl
example (model : DomainModel) : (producer model).events.length = 2 := by kernel_rfl
example (model : DomainModel) : (validator model).events.length = 2 := by kernel_rfl

-- Omitting private capabilities refuses before the first public query.
example (model : DomainModel) :
    (Domain.produce model Local.program Local.context Local.Producer.participant
      [.transcript suite []] (Execution.fixedOracle model.toCarriers) 0).events = [] := by kernel_rfl
example (model : DomainModel) :
    (Domain.produce model Local.program Local.context Local.Producer.participant
      [.transcript suite []] (Execution.fixedOracle model.toCarriers) 0).outcome =
        .stopped .refused := by kernel_rfl

-- Failed public queries retain the entire unused proof and do not observe the
-- source delivery. The source and constructed handlers share this behavior.
example (model : DomainModel) :
    (Domain.validate model Scalar.program Scalar.context Scalar.Validator.participant
      [.transcript suite []] [.index 7] (Execution.failedOracle model.toCarriers) 41).state.proof =
        [.index 7] := by kernel_rfl

-- Source/private bound 3 is formed, but the native transcript operation
-- refuses it before a query, even when its dynamic value matches the request.
example (carriers : Carriers) :
    Domain.challengeRequest Scalar.context suite (.sampleIndex 3) Scalar.queryTemplate 0 2 [1]
      [.data .index, .transcript suite]
      ([.transcript suite [], .data (.index 3), .indices []] : Domain.Environment carriers) =
        .halt .refused := by kernel_rfl
example (carriers : Carriers) :
    Domain.challengeRequest Block.context suite (.sampleIndices 8 1048577) Block.queryTemplate 0 1 []
      [.data .indices, .transcript suite]
      ([.transcript suite [], .indices []] : Domain.Environment carriers) =
        .halt .refused := by kernel_rfl

end Tests.IndexServices.Private
