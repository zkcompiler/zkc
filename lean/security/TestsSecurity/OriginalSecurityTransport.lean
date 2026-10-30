module

import ZkcSecurity.Claims.Methods.LosslessPresentationClaims
import Zkc.Construction.OriginalExecution

set_option autoImplicit false
namespace TestsSecurity.OriginalSecurityTransport
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir

abbrev carriers := Structured.uniformCarriers Nat Nat
def frame : Domain.Environment carriers := [.data (.index 7)]
def source : PIR.Process (Domain.effects carriers) Nat :=
  .call (.receive .boolean "decision" "decision" "prover") fun decision =>
    if decision then .done 7 else .halt .reject
def actual : PIR.Process (Domain.effects carriers) (Nat × Domain.Environment carriers) :=
  .call (.checkpoint frame) fun _ =>
  .call (.receive .boolean "decision" "decision" "prover") fun decision =>
    if decision then .done (7, frame) else .halt .reject

def simulation : Zkc.Construction.Original.Simulation
    (fun left right => right = (left, frame)) (fun _ reached => reached = frame) source actual := by
  unfold source actual
  apply Zkc.Construction.Original.Simulation.checkpoint frame rfl
  apply Zkc.Construction.Original.Simulation.call (.receive .boolean "decision" "decision" "prover")
  intro decision
  cases decision
  · exact .halt .reject
  · exact .done rfl

variable (query : Domain.History carriers → (event : Domain.Event carriers) → Id (Domain.Raw event))

example (proof : Domain.Proof carriers) :
    (fun result => (mapOutcome Prod.fst result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution query actual proof =
      (fun result => (mapOutcome id result.1, result.2)) <$>
        ZkcSecurity.Endpoint.Domain.readExecution query source proof :=
  Original.readExecution simulation id Prod.fst (fun _ _ related => by rw [related]; rfl) query proof

example (suffix : Domain.Proof carriers) :
    ZkcSecurity.Endpoint.Domain.readExecution query actual (.boolean false :: suffix) =
      pure (.stopped .reject, suffix) := rfl

example (suffix : Domain.Proof carriers) :
    ZkcSecurity.Endpoint.Domain.readExecution query actual (.boolean true :: suffix) =
      pure (.returned (7, frame), suffix) := rfl

/-- A malformed proof head is not consumed, even after an actual checkpoint. -/
example (suffix : Domain.Proof carriers) :
    ZkcSecurity.Endpoint.Domain.readExecution query actual (.index 8 :: suffix) =
      pure (.stopped .refused, .index 8 :: suffix) := rfl

example : ZkcSecurity.Endpoint.Domain.readExecution query actual [] =
    pure (.stopped .refused, []) := rfl

#print axioms Original.readExecution
#print axioms Original.coherent
#print axioms Original.Alignment.cost
#print axioms Original.Alignment.derivation
#print axioms Original.Claims.Installation.losslessChargedExport
#print axioms Zkc.Construction.Original.Simulation.source_run_interaction

end TestsSecurity.OriginalSecurityTransport
