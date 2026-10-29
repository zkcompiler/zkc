import Zkc.Construction.SourceConnection
import ZkcExamples.Structured.Generated.Connections.SmallSumcheck

/-! The semantic contract fixes source input order before selecting a proof
method. These controls concern the connection boundary, not cryptographic
properties or receipt authorization. -/
set_option autoImplicit false
noncomputable section
namespace Tests.SourceConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open SourceConnection

private theorem wrapper {P : Prop} (proof : P) : P := proof

open ZkcExamples.Structured.Generated.Connections.SmallSumcheck in
theorem validatorConnection : Connected program validatorRouting context.validator
    validator.inputs.abi validatorArtifact :=
  wrapper (ofRootCertificate validator (by kernel_rfl))

open ZkcExamples.Structured.Generated.Connections.SmallSumcheck in
theorem producerConnection : Connected program producerRouting context.producer
    producer.inputs.abi producerArtifact :=
  wrapper (ofRootCertificate producer (by kernel_rfl))

-- Scope preservation is weaker than canonical presence and input order.
example : ConnectionFrame.inputScopes 1 [[1], [1]] [.absent, .absent] = true := rfl
example : ConnectionRootInputs.inputLocations 1 [] [.index, .index] [[1], [1]] 0 0 =
    .ok [.data 0, .data 1] := rfl
example : ConnectionRootInputs.inputLocations 1 [] [.index, .index] [[1], [1]] 0 0 ≠
    .ok [.absent, .absent] := by decide
example : ConnectionRootInputs.inputLocations 1 [] [.index, .index] [[1], [1]] 0 0 ≠
    .ok [.data 1, .data 0] := by decide

#print axioms validatorConnection
#print axioms producerConnection
end Tests.SourceConnection
