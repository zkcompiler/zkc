import Zkc.IR.Source.Structured.CommonCoordinateReport
import Zkc.Tests.IR.OracleCommonCoordinateScalaractualData
import Zkc.Tests.IR.OracleCommonCoordinateScalarwrapperData
import Zkc.Tests.IR.OracleCommonCoordinateBlockactualData
import Zkc.Tests.IR.OracleCommonCoordinateBlockwrapperData

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured CommonCoordinate
namespace Tests.OracleCommonCoordinateSlices

/- This is a complete retained-body coordinate phase, not canonical subject admission.
The separate Full test deliberately keeps the parent's component-metadata refusal. -/
private def bodies (source : Snapshot) : Except String (List CheckedProtocol) := do
  let domains ← source.domains.mapM Domain.resolve
  let headers ← collectProtocolHeaders source
  let summaries ← source.identitySummaries
  let helpers ← checkUnitHelpers source domains summaries
  checkUnitProtocols source domains summaries headers helpers

def audit (label : String) (source : Snapshot) : IO Unit := do
  let definitions ← match bodies source with
    | .error code => throw (IO.userError (label ++ ": retained bodies: " ++ code))
    | .ok definitions => pure definitions
  let certificate ← match certify source definitions with
    | .error code => throw (IO.userError (label ++ ": coordinate: " ++ code))
    | .ok certificate => pure certificate
  let selections := certificate.selections
  let sites := (selections.map fun (_, selection) ↦
    (selection.location.definition, selection.location.row)).eraseDups
  unless sites.length == 4 do
    throw (IO.userError (label ++ ": expected four source selection sites; " ++ toString sites))
  let noInputs := selections.all fun (_, selection) ↦ selection.requirements.all fun requirement ↦
    match requirement with | .counter .. => true | .input .. => false
  unless noInputs do throw (IO.userError (label ++ ": unexpected input coordinate requirement"))
  IO.println (label ++ ": body-only; all " ++ toString source.definitions.length ++
    " definitions retained; " ++ toString definitions.length ++
    " protocols; four selection sites=" ++ toString sites)
  for (_, selection) in selections do
    IO.println ("  row=" ++ toString selection.location.row ++
      "; requirements=" ++ reprStr selection.requirements)


end Tests.OracleCommonCoordinateSlices
