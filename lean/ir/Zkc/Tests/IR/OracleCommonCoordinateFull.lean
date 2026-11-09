import Zkc.IR.Source.Structured.OracleIngress
import Zkc.IR.Source.Structured.CommonCoordinateReport
import Zkc.Tests.IR.OracleCommonCoordinateScalaractualData
import Zkc.Tests.IR.OracleCommonCoordinateScalarwrapperData
import Zkc.Tests.IR.OracleCommonCoordinateBlockactualData
import Zkc.Tests.IR.OracleCommonCoordinateBlockwrapperData

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
open CommonCoordinate
namespace Tests.OracleCommonCoordinateFull

def audit (label : String) (source : Snapshot) : IO Unit := do
  let imported : Imported source ← match admitted : check source with
    | .error code => throw (IO.userError (label ++ ": import: " ++ code))
    | .ok program => pure ⟨program, admitted⟩
  let subject ← match imported.oracleSubject with
    | .error code => throw (IO.userError (label ++ ": subject: " ++ code))
    | .ok subject => pure subject
  let selections := subject.coordinates.selections
  let sites := (selections.map fun (_, selection) ↦
    (selection.location.definition, selection.location.row)).eraseDups
  unless sites.length == 4 do
    throw (IO.userError (label ++ ": expected four retained selection sites: " ++ toString sites))
  IO.println (label ++ ": source=" ++ source.source ++ "; definitions=" ++
    toString source.definitions.length ++ "; protocols=" ++
    toString imported.program.payload.protocols.length ++ "; sites=" ++ toString sites)
  for (pair, selection) in selections do
    IO.println ("  pair=" ++ reprStr pair ++ "; definition=" ++
      toString selection.location.definition ++ "; row=" ++ toString selection.location.row ++
      "; requirements=" ++ reprStr selection.requirements)


end Tests.OracleCommonCoordinateFull
