import Zkc.Source.Structured.Import
import ZkcTools.SourceClaims.Components

/-! Production source exports and exact boundary controls. Association data
establishes no helper, method, operational-domain or security law. -/
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.ComponentBoundaries

private def expect {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error code => throw (IO.userError code)

private def refuses {α : Type} (value : Except String α) (code : String) : Bool :=
  match value with | .error actual => actual == code | _ => false

def run (path : System.FilePath) : IO Unit := do
  let cases ← expect (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (condition : Bool) : IO Unit := do
    count.modify (· + 1)
    unless condition do failures.modify (· ++ [name])
  for entry in cases do
    let fields ← expect entry.getArr?
    let name ← expect fields[0]!.getStr?
    let snapshotText ← IO.FS.readFile (← expect fields[1]!.getStr?)
    let snapshot ← expect (Format.parse snapshotText >>= Format.snapshot)
    let _ ← expect (check snapshot)
    test s!"{name}: whole-unit admission" true
    let expected ← expect fields[2]!.getStr?
    if expected.startsWith "component-" then
      test s!"{name}: exact independent refusal" (refuses (ComponentRoutes.derive snapshot) expected)
    else
      let text ← IO.FS.readFile expected
      test s!"{name}: exact native/Lean association" (ZkcTools.SourceClaims.Components.check snapshot text).isOk
      let wire ← expect (ZkcTools.SourceClaims.Components.parse text >>= ZkcTools.SourceClaims.Components.decode snapshot)
      if name.startsWith "slots-" then
        test s!"{name}: exactly 512 deduplicated slots"
          (wire.proposals.length == 1 && wire.proposals.all (·.slots.length == 512))
      else
        let inputs := wire.seams.filter fun row => match row.endpoint with
          | .repeatInput .. => true | _ => false
        test s!"{name}: count and ordinary boundary inputs retained" (!inputs.isEmpty)
        let changed := { wire with seams := wire.seams.filter fun row => match row.endpoint with
          | .repeatInput .. => false | _ => true }
        test s!"{name}: dropping ordinary source association refuses"
          (refuses (ComponentExport.check snapshot changed) "component-seam-association")
        let changed := { wire with seams := wire.seams.map fun row =>
          if row.kind == .method then { row with kind := .pure } else row }
        unless name.startsWith "pure" do
          test s!"{name}: loop action cannot be relabeled pure"
            (refuses (ComponentExport.check snapshot changed) "component-seam-association")
    IO.println s!"checked component boundary: {name}"
  let descriptors ← expect (Json.parse (← IO.FS.readFile (path.parent.getD "." / "descriptor-cases.json")) >>= Json.getArr?)
  for entry in descriptors do
    let fields ← expect entry.getArr?
    let name ← expect fields[0]!.getStr?
    let valid ← expect fields[2]!.getBool?
    test s!"descriptor {name}" ((Format.descriptor fields[1]!).isOk == valid)
    for tag in ["pure", "terminal", "action"] do
      let route := Json.arr #[.str tag, fields[1]!, .arr #[], toJson (0 : Nat), .str "V", .arr #[]]
      test s!"route {tag} descriptor {name}" ((ComponentExport.route 65 route).isOk == valid)
  for failure in ← failures.get do IO.eprintln failure
  unless (← failures.get).isEmpty do throw (IO.userError "component boundary controls failed")
  IO.println s!"component boundaries: {← count.get} checks passed"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected native boundary manifest")
  Tests.ComponentBoundaries.run path

end Tests.ComponentBoundaries
