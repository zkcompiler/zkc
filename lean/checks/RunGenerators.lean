import Tests.StructuredBindingsGenerator
import Tests.StructuredBindingsDispatchGenerate
import Tests.Constructed.Generate
import Tests.StructuredNormalFormComponents
import Tests.StructuredPresentation
import ZkcTools.StructuredSource.Discovery.Main

/-! Executable dispatch only. The imported namespaced implementations remain
in the whole-library audit and may be imported together. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "bindings" :: rest => Tests.StructuredBindingsGenerator.main rest; return 0
  | "dispatch-controls" :: rest => Tests.StructuredBindingsDispatchGenerate.main rest; return 0
  | "constructed" :: rest => Tests.Constructed.Generate.main rest; return 0
  | "component-controls" :: rest => Tests.StructuredNormalFormComponents.main rest; return 0
  | "presentation-controls" :: rest => Tests.StructuredPresentation.main rest; return 0
  | "discovery" :: rest => ZkcTools.StructuredSource.Discovery.Driver.main rest
  | _ => throw (IO.userError "expected bindings, dispatch-controls, constructed, component-controls, presentation-controls or discovery")
