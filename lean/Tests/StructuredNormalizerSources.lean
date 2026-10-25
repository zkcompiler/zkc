import Zkc.Source.Structured.Bindings.Assembly
import ZkcExamples.Structured.SumcheckSourceViews
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

/-! Actual admitted source regressions for arbitrary producer guards and a
nonprojection Math conjunction in the composed verifier. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.StructuredNormalizerSources
open Zkc.Source Zkc.Source.Structured NormalForm Bindings

abbrev small := ZkcExamples.Structured.SumcheckSourceViews.program
abbrev composed := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program

/-- Exact helper calls are kept; no laws about the helpers' results are assumed. -/
def smallSignature : Signature := {kept := small.payload.definitions.map (·.helper)}

def smallDefinition : CheckedProtocol := small.payload.protocols.get ⟨0, by decide +kernel⟩

example : (normalize smallSignature smallDefinition.body 0 2 (optionalPattern smallDefinition.inputs)).isOk = true := by
  kernel_rfl

/-- One key per actual callee role, with its complete optional-component ABI. -/
def calleeKeys : List CalleeKey :=
  composed.payload.protocols.flatMap fun definition =>
    (List.range definition.roles.length).map fun role =>
      ⟨definition.signature, role, optionalPattern definition.inputs, []⟩

def composedSignature : Signature :=
  {kept := composed.payload.definitions.map (·.helper), callees := calleeKeys}

def composedDefinition : CheckedProtocol := composed.payload.protocols.get ⟨1, by decide +kernel⟩

example : (normalize composedSignature composedDefinition.body 1 2 (optionalPattern composedDefinition.inputs)).isOk = true := by
  kernel_rfl

end Tests.StructuredNormalizerSources
