module

public import ZkcTools.StructuredSource.Presentation
public import Zkc.Source.Structured.UnitViews

@[expose] public section

/-! Lean-owned serialization of typed admitted bodies. The emitted
`structured_views` command checks each admission phase against the retained
snapshot; running the printer supplies no proof or semantic authority. -/

namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource.Presentation

mutual
  def helperRegionText {inputs outputs : List Ty} : Region dialect inputs outputs → String
    | .ret values => app ".ret" [operandsText values]
    | .stop reason => app ".stop" [stopText reason]
    | .bind body next => app ".bind" [helperRegionText body, helperRegionText next]
    | .letOp op args bodies next => app ".letOp" [opText op, operandsText args,
        helperRegionsText bodies, helperRegionText next]
  def helperRegionsText {signatures : List (List Ty × List Ty)} : Regions dialect signatures → String
    | .nil => ".nil"
    | .cons body rest => app ".cons" [helperRegionText body, helperRegionsText rest]
end

def inputsSource (program : Program) (moduleName dataModule : String) : String := Id.run do
  let mut text := "module\n\npublic import Zkc.Source.Structured.UnitViews\npublic import " ++
    dataModule ++ "\n\n@[expose] public section\n\n/-! Generated typed bodies and phased admission. -/\nnamespace " ++
    moduleName ++ "\nopen Zkc.Source Zkc.Source.Structured\n" ++
    "set_option smartUnfolding false\nset_option maxRecDepth 50000\nset_option maxHeartbeats 16000000\nnoncomputable section\n\n"
  for (definition, index) in program.payload.definitions.zipIdx do
    let name := "helper" ++ toString index
    text := text ++ "abbrev " ++ name ++ "Helper : Helper := " ++ helperText definition.helper ++
      "\ndef " ++ name ++ "Body : Region dialect " ++ name ++ "Helper.inputs " ++ name ++
      "Helper.outputs :=\n  " ++ helperRegionText definition.body ++ "\n\n"
  for (definition, index) in program.payload.protocols.zipIdx do
    let name := "protocol" ++ toString index
    text := text ++ "def " ++ name ++ "Signature : ProtocolSignature := " ++ signatureText definition.signature ++
      "\ndef " ++ name ++ "Body : Region protocolDialect " ++ name ++ "Signature.inputs " ++ name ++
      "Signature.outputs :=\n  " ++ regionText definition.body ++ "\n\n"
  text := text ++ "structured_views " ++ dataModule ++ ".snapshot\n  helpers [" ++
    ", ".intercalate (program.payload.definitions.zipIdx.map fun (_, i) => "helper" ++ toString i) ++
    "]\n  protocols [" ++
    ", ".intercalate (program.payload.protocols.zipIdx.map fun (_, i) => "protocol" ++ toString i) ++
    "]\n\nend\nend " ++ moduleName ++ "\n"
  return text

end ZkcTools.StructuredSource.Bindings
