module

public import Zkc.Source.Structured.UnitViews
public import Tests.StructuredBindingsGeneric

@[expose] public section

/-! Generated typed bodies and phased admission. -/
namespace Tests.Generated.StructuredBindingsGenericInputs
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

def protocol0Signature : ProtocolSignature := (⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature)
def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  (.letOp (.mark "round") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round") (.cons .here (.cons (.there .here) .nil)) (.cons (.ret (.cons (.there .here) .nil)) .nil) (.ret (.cons .here .nil))))

structured_views Tests.StructuredBindingsGeneric.snapshot
  helpers []
  protocols [protocol0]

end
end Tests.Generated.StructuredBindingsGenericInputs
