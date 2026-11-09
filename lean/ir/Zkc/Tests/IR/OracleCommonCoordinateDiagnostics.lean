import Zkc.Tests.IR.OracleCommonCoordinateFull

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
namespace Tests.OracleCommonCoordinateDiagnostics

private def descriptorName : OracleDescriptor → String
  | .input .. => "input"
  | .components .. => "components"
  | .virtual .. => "virtual"
  | _ => "other"

private def audit (label : String) (source : Snapshot) : IO Unit := do
  IO.println (label ++ ": unchanged complete source; definitions=" ++
    toString source.definitions.length)
  let domains ← match source.domains.mapM Domain.resolve with
    | .error code => throw (IO.userError code)
    | .ok domains => pure domains
  let headers ← match collectProtocolHeaders source with
    | .error code => throw (IO.userError code)
    | .ok headers => pure headers
  let summaries ← match source.identitySummaries with
    | .error code => throw (IO.userError code)
    | .ok summaries => pure summaries
  let mut selections := 0
  for (definition, index) in source.definitions.zipIdx do
    match definition with
    | .function function =>
      if function.kind == .protocol then
        match checkProtocol source domains summaries function headers with
        | .error code => IO.println ("  lower blocked at definition=" ++ toString index ++
            " " ++ function.name ++ ": " ++ code)
        | .ok _ => pure ()
      let rows := function.body.oracleRows Limits.nesting [7]
      let actions := function.body.storedInstructions.filter fun action ↦ match action with
        | .instruction (.oracle _) .. => true
        | _ => false
      for (action, (descriptor, row)) in actions.zip rows do
        match action, descriptor with
        | .instruction _ operands _ _ _, .sequenceAt .. =>
          selections := selections + 1
          IO.println ("  retained selection definition=" ++ toString index ++
            "; row=" ++ toString row ++ "; original operands=" ++ toString operands)
        | .instruction _ _ _ _ site, .virtual ..
        | .instruction _ _ _ _ site, .input ..
        | .instruction _ _ _ _ site, .components .. =>
          if site.isEmpty then
            IO.println ("  parent-required empty site definition=" ++ toString index ++
              "; row=" ++ toString row ++ "; op=" ++ descriptorName descriptor)
        | _, _ => pure ()
    | _ => pure ()
  unless selections == 4 do throw (IO.userError "source inventory changed")

#eval audit "scalar actual" Tests.FullFri.ScalarLowDegree.Actual.snapshot
#eval audit "scalar wrapper" Tests.FullFri.ScalarLowDegree.Wrapper.snapshot
#eval audit "block actual" Tests.FullFri.BlockLowDegree.Actual.snapshot
#eval audit "block wrapper" Tests.FullFri.BlockLowDegree.Wrapper.snapshot

end Tests.OracleCommonCoordinateDiagnostics
