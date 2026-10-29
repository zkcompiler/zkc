module

import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
import ZkcExamples.Structured.Generated.Connections.TwoSums

/-! Full return ABI controls at the generic source connection boundary.
These checks cover both actual roots and both roles, independently of any
family-specific callback tuple or template-matching implementation. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ConnectionABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionInstallation
open ZkcExamples.Structured.Generated.Connections

namespace SmallSumcheckControls
open SmallSumcheck

example : (ReturnLayout.build program.payload.entry.signature context context.producer producerArtifact).isOk = true := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.producer { producerArtifact with returned := producerArtifact.returned.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.producer { producerArtifact with returned := producerArtifact.returned ++ [0] }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.producer { producerArtifact with outputs := .data (.field "other") :: producerArtifact.outputs.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature
    (context.mapReplacement (fun replacement => { replacement with suite := "other" }))
    context.producer producerArtifact).toOption = none := by decide +kernel

example : (ReturnLayout.build program.payload.entry.signature context context.validator validatorArtifact).isOk = true := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.validator { validatorArtifact with returned := validatorArtifact.returned.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.validator { validatorArtifact with returned := validatorArtifact.returned ++ [0] }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.validator { validatorArtifact with outputs := .data (.field "other") :: validatorArtifact.outputs.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature
    (context.mapReplacement (fun replacement => { replacement with suite := "other" }))
    context.validator validatorArtifact).toOption = none := by decide +kernel

-- Policy admission has its own owner; selecting a connection does not bypass it.
example : checkCompiled ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported
    { validatorArtifact with policy := { validatorArtifact.policy with suite := "other" } } =
    .error "construction-inputs" := by decide +kernel
end SmallSumcheckControls

namespace TwoSumsControls
open TwoSums

example : (ReturnLayout.build program.payload.entry.signature context context.producer producerArtifact).isOk = true := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.producer { producerArtifact with returned := producerArtifact.returned.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.producer { producerArtifact with returned := producerArtifact.returned ++ [0] }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.producer { producerArtifact with outputs := .data (.field "other") :: producerArtifact.outputs.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature
    (context.mapReplacement (fun replacement => { replacement with suite := "other" }))
    context.producer producerArtifact).toOption = none := by decide +kernel

example : (ReturnLayout.build program.payload.entry.signature context context.validator validatorArtifact).isOk = true := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.validator { validatorArtifact with returned := validatorArtifact.returned.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.validator { validatorArtifact with returned := validatorArtifact.returned ++ [0] }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature context context.validator { validatorArtifact with outputs := .data (.field "other") :: validatorArtifact.outputs.tail }).toOption = none := by decide +kernel
example : (ReturnLayout.build program.payload.entry.signature
    (context.mapReplacement (fun replacement => { replacement with suite := "other" }))
    context.validator validatorArtifact).toOption = none := by decide +kernel

-- Policy admission has its own owner; selecting a connection does not bypass it.
example : checkCompiled ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported
    { validatorArtifact with policy := { validatorArtifact.policy with suite := "other" } } =
    .error "construction-inputs" := by decide +kernel
end TwoSumsControls
end TestsSecurity.ConnectionABI
