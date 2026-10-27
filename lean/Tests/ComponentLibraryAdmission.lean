import Zkc.Source.Structured.Import
import ZkcTools.SourceClaims.Components

/-! Selected clause-free library roots retain structural resource ownership.
Their admission supplies no relation law or final acceptance evidence. -/
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.ComponentLibraryAdmission

private def expect {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error code => throw (IO.userError code)

private def refuses {α : Type} (value : Except String α) (code : String) : Bool :=
  match value with | .error actual => actual == code | _ => false

def run (path : System.FilePath) : IO Unit := do
  let entries ← expect (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let count ← IO.mkRef 0
  let failures ← IO.mkRef ([] : List String)
  let test (name : String) (condition : Bool) : IO Unit := do
    count.modify (· + 1)
    unless condition do failures.modify (· ++ [name])
  for entry in entries do
    let fields ← expect entry.getArr?
    let name ← expect fields[0]!.getStr?
    let snapshot ← expect (Format.parse (← IO.FS.readFile (← expect fields[1]!.getStr?)) >>= Format.snapshot)
    let claims ← IO.FS.readFile (← expect fields[2]!.getStr?)
    let source := snapshot.sourceDeclarations
    let headers ← expect (collectProtocolHeaders snapshot)
    let root ← expect (requireSome (source.protocols.find? (·.name == snapshot.entry)) "missing root")
    let contract ← expect (requireSome (snapshot.contracts.find? (·.owner == snapshot.entry)) "missing contract")
    test s!"{name}: selected root has a clause-free linear residual"
      (contract.clauses.isEmpty && root.outputs.any (source.isLinear ·.type))
    let _ ← expect (check snapshot)
    test s!"{name}: exact maintained whole-unit admission" true
    let routes ← expect (ComponentRoutes.derive snapshot)
    test s!"{name}: selected residual is covered" (routes.seams.any fun row =>
      row.caller == snapshot.entry && match row.endpoint with | .residual _ => true | _ => false)
    test s!"{name}: exact independent native association"
      (ZkcTools.SourceClaims.Components.check snapshot claims).isOk
    let child ← expect (requireSome (source.protocols.find? fun protocol =>
      protocol.inputs.any (source.isLinear ·.type)) "missing linear input protocol")
    let selected : Snapshot := { snapshot with entry := child.name }
    test s!"{name}: independent selection also admits linear inputs" (check selected).isOk
    test s!"{name}: association remains fixed to the requested root"
      (refuses (ZkcTools.SourceClaims.Components.check selected claims) "source-claim-original")
    let exported ← expect (ZkcTools.SourceClaims.Components.parse claims >>= ZkcTools.SourceClaims.Components.decode snapshot)
    let changed := { exported with seams := exported.seams.filter (·.caller != snapshot.entry) }
    test s!"{name}: dropping selected residual rows refuses"
      (refuses (ComponentExport.check snapshot changed) "component-seam-association")
    let changed := { exported with seams := exported.seams.map fun row =>
      if row.caller == snapshot.entry then { row with endpoint := .residual 999 } else row }
    test s!"{name}: wrong selected residual endpoint refuses"
      (refuses (ComponentExport.check snapshot changed) "component-seam-association")
    let changed : SourceDeclarations := { source with records := source.records.map fun record =>
      if record.resource == "linear" then { record with sealed := false } else record }
    test s!"{name}: unsealed linear declaration refuses"
      (refuses (changed.check snapshot headers) "component-declaration-record")
    let changed : SourceDeclarations := { source with protocols := source.protocols ++ [root] }
    test s!"{name}: duplicate source owner refuses"
      (refuses (changed.check snapshot headers) "component-declaration-owner")
    let changed : SourceDeclarations := { source with protocols := source.protocols.map fun protocol =>
      if protocol.name != snapshot.entry then protocol else
        { protocol with outputs := protocol.outputs.map fun port =>
          if source.isLinear port.type then { port with roles := [] } else port } }
    test s!"{name}: exact holder scope is required even without clauses"
      (refuses (changed.check snapshot headers) "component-declaration-role")
    let pending ← expect (requireSome (root.outputs.find? (source.isLinear ·.type)) "missing linear output")
    test s!"{name}: maintained residual has multiple fields" (pending.count > 1)
    for duplicate in [true, false] do
      let changed : Snapshot := { snapshot with definitions := snapshot.definitions.map fun
        | .function function =>
          if function.name != snapshot.entry then .function function else
            let .block instructions terminator := function.body
            let terminator := match terminator with
              | .ret indices => .ret (indices.set (pending.offset + 1)
                  (if duplicate then indices[pending.offset]?.getD 0 else 999))
              | other => other
            .function { function with body := .block instructions terminator }
        | other => other }
      test s!"{name}: duplicate or missing selected residual field {duplicate} refuses"
        (refuses (ComponentRoutes.derive changed)
          (if duplicate then "component-seam-coverage" else "component-seam-reference"))
    let changed : Snapshot := { snapshot with contracts := snapshot.contracts.map fun contract =>
      { contract with clauses := contract.clauses.map fun clause => { clause with residual := none } } }
    test s!"{name}: contracted output still requires its retained relation"
      (refuses (source.check changed headers) "component-claim-relation")
    let changed : Snapshot := { snapshot with contracts := snapshot.contracts.map fun contract =>
      { contract with clauses := contract.clauses.map fun clause =>
        { clause with residual := clause.residual.map fun application =>
          { application with relation := "different-relation" } } } }
    test s!"{name}: same closed linear type cannot change relation"
      (refuses (source.check changed headers) "component-claim-relation")
    IO.println s!"checked selected library root: {name}"
  for failure in ← failures.get do IO.eprintln failure
  unless (← failures.get).isEmpty do throw (IO.userError "library admission controls failed")
  IO.println s!"component library admission: {← count.get} checks passed"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected library snapshot/claims manifest")
  Tests.ComponentLibraryAdmission.run path

end Tests.ComponentLibraryAdmission
