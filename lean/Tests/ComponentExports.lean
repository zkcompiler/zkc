import Zkc.Source.Structured.ComponentChecking
import ZkcTools.SourceClaims.Components
import ZkcTools.StructuredSource.OpenEvaluation

/-! Native-capture integration controls. Supply the snapshot and source-claims
export of compiler/test/fixtures/source-claims/components.zkc. Mutations are
checked independently of the compiler's serializer. -/
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.ComponentExports

private def expect {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error code => throw (IO.userError code)
private def field (json : Json) (name : String) : Json :=
  (json.getObjVal? name).toOption.getD .null
private def array (json : Json) : Array Json := json.getArr?.toOption.getD #[]
private def setField (json : Json) (name : String) (value : Json) : Json :=
  Json.mkObj ((json.getObj?.toOption.map (·.toList) |>.getD []).map fun (key, old) =>
    (key, if key == name then value else old))
private def source (wire : Json) (call : Nat) (value : Json) : Json := Id.run do
  let mut calls := array (field wire "proposals")
  let mut proposal := array calls[call]!
  let mut slots := array proposal[5]!
  let mut slot := array slots[0]!
  slot := slot.set! 2 value
  slots := slots.set! 0 (.arr slot)
  proposal := proposal.set! 5 (.arr slots)
  calls := calls.set! call (.arr proposal)
  return setField wire "proposals" (.arr calls)
private def arr (items : List Json) : Json := .arr items.toArray
private def refuses {α : Type} (checked : Except String α) (code : String) : Bool :=
  match checked with | .error actual => actual == code | _ => false

-- Structural acceptance needs the actual conjunction path. Its proof uses no
-- relation theorem and cannot certify a terminal's mathematical adequacy.
example (leaf other : SeamRoute) : AcceptancePath leaf
    (.pure .booleanAnd [2] 0 "V" [other, leaf]) := .right [2] 0 "V" .here

private def changeFunctions (snapshot : Snapshot) (change : Function → Function) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map (fun
    | .function func => .function (change func)
    | other => other) }

private def run (snapshot : Snapshot) (text : String) : IO Unit := do
  let checks ← IO.mkRef 0
  let test (name : String) (condition : Bool) : IO Unit := do
    checks.modify (· + 1)
    unless condition do throw (IO.userError s!"component export failed: {name}")
  let wire ← expect (ZkcTools.SourceClaims.Components.parse text)
  let exported ← expect (ZkcTools.SourceClaims.Components.decode snapshot wire)
  let derived ← expect (ComponentRoutes.derive snapshot)
  test "native admission and exact independent association"
    (ZkcTools.SourceClaims.Components.check snapshot text).isOk
  test "three actual occurrences" (exported.proposals.length == 3)
  test "zero loop retains both alternatives" (exported.seams.any fun row =>
    match row.endpoint with | .repeatResult .. => row.routes.length == 2 | _ => false)
  test "terminal exit" (exported.seams.any fun row => row.kind == .terminal)
  test "derived contexts carry actual SSA types" (derived.calls.all fun context =>
    context.proposal.operands.all (· < context.types.length))
  let program ← expect (check snapshot)
  for count in [0, 1, 2] do
    for value in [false, true] do
      let observed ← expect (ZkcTools.StructuredSource.evaluateOpen program (arr [
        .str "zkc.structured-open-request/0", .str "role00000000", arr [.bool value, .str (toString count)],
        arr [], toJson (100000 : Nat)]))
      test s!"actual execution, count={count}, value={value}"
        ((array observed)[1]? == some (arr [.str "returned", arr [.bool value]]))
  let role := "role00000000"
  for value in [arr [.str "operand", toJson (0 : Nat), .str role],
      arr [.str "parameter", arr [.str "input", toJson (0 : Nat), .str role]]] do
    test "typed logical source" (ZkcTools.SourceClaims.Components.check snapshot (source wire 0 value).compress).isOk
  let calls := array (field wire "proposals")
  let first := (array calls[0]!)[1]!
  let second := (array calls[1]!)[1]!
  test "dominating actual result" (ZkcTools.SourceClaims.Components.check snapshot
    (source wire 1 (arr [.str "result", first, toJson (1 : Nat), .str role])).compress).isOk
  let relation ← expect (requireSome snapshot.relations.head? "fixture relation")
  let formula := relation.formula.getD ""
  test "defined Math term" (ZkcTools.SourceClaims.Components.check snapshot
    (source wire 0 (arr [.str "math", .str formula, toJson (0 : Nat), arr [
      arr [.str "operand", toJson (0 : Nat), .str role],
      arr [.str "operand", toJson (0 : Nat), .str role]]])).compress).isOk
  for value in [arr [.str "operand", toJson (0 : Nat), .str "wrong-role"],
      arr [.str "operand", toJson (99 : Nat), .str role],
      arr [.str "witness", arr [.str "input", toJson (0 : Nat), .str role]],
      arr [.str "parameter", arr [.str "output", toJson (0 : Nat), .str role]],
      arr [.str "result", second, toJson (0 : Nat), .str role],
      arr [.str "result", first, toJson (99 : Nat), .str role],
      arr [.str "math", .str "missing", toJson (0 : Nat), arr []],
      arr [.str "math", .str formula, toJson (0 : Nat), arr [arr [.str "open"], arr [.str "open"]]],
      arr [.str "open", .null]] do
    let outcome := ZkcTools.SourceClaims.Components.check snapshot (source wire 0 value).compress
    test s!"invalid instantiation {value.compress}: {repr outcome}" (refuses outcome "component-instantiation")
  let witnessSnapshot := { snapshot with relations := snapshot.relations.map fun relation =>
    { relation with purposes := ["witness", "statement"] } }
  let witnessWire : ComponentExport.Export := { exported with proposals := exported.proposals.map fun proposal =>
    { proposal with slots := proposal.slots.map fun slot => { slot with purpose := "witness", source := .witness ⟨.input, 0, role, false⟩ } } }
  test "declared caller witness uses the same assignment store" (ComponentExport.check witnessSnapshot witnessWire).isOk
  test "missing seam" (refuses (ZkcTools.SourceClaims.Components.check snapshot
    (setField wire "seams" (arr [])).compress) "component-seam-association")
  test "duplicate proposal" (refuses (ZkcTools.SourceClaims.Components.check snapshot
    (setField wire "proposals" (.arr (calls.push calls[0]!))).compress) "component-instantiation")
  let changed := (array calls[0]!).set! 2 (.str "wrong-body")
  test "wrong actual callee" (refuses (ZkcTools.SourceClaims.Components.check snapshot
    (setField wire "proposals" (.arr (calls.set! 0 (.arr changed)))).compress) "component-instantiation")
  test "unknown field" (refuses (ZkcTools.SourceClaims.Components.check snapshot
    (Json.mkObj ((wire.getObj?.toOption.get!).toList ++ [("unknown", .bool true)])).compress)
    "source-claim-fields")
  for duplicate in ["\"seams\":[],", "\"se\\u0061ms\":[],"] do
    test "duplicate and escaped duplicate keys" (refuses
      (ZkcTools.SourceClaims.Components.parse ("{" ++ duplicate ++ text.drop 1))
      "source-claim-duplicate")
  let declarations := snapshot.sourceDeclarations
  test "missing residual declaration relation" (refuses
    (check { snapshot with contracts := snapshot.contracts.map fun contract =>
      if contract.clauses.any (·.kind == .continuation) then
        { contract with clauses := contract.clauses.map fun clause => { clause with residual := none } }
      else contract }) "structured-contract-residual")
  test "wrong retained source role" (!(check { snapshot with sourceDeclarations :=
    { declarations with protocols := declarations.protocols.map fun protocol =>
      { protocol with inputs := protocol.inputs.map fun port => { port with roles := ["absent"] } } } }).isOk)
  test "duplicate retained record" (refuses (check { snapshot with sourceDeclarations :=
    { declarations with records := declarations.records ++ declarations.records } }) "component-declaration-duplicate")
  -- These controls exercise the bounded route function directly. Admission is
  -- tested above; malformed mutations are not claimed to be valid source units.
  let transform (descriptor : Descriptor) : Snapshot := changeFunctions snapshot fun func =>
    if func.kind == .local then { func with body := .block [.instruction descriptor [] [.boolean] [] "changed"] (.ret [0]) } else func
  for (descriptor, code) in [(Descriptor.draw role scalarDomain, "component-seam-sampling"),
      (.exchange role role, "component-seam-message"),
      (.exec "oracle.query" "" [], "component-seam-oracle"),
      (.exec "unknown.effect" "" [], "component-seam-effect")] do
    test code (refuses (ComponentRoutes.derive (transform descriptor)) code)
  let stopped := changeFunctions snapshot fun func =>
    if func.kind == .local then { func with body := .block [] (.stop .abort "stop") } else func
  test "stopped helper has no effect obligation" (ComponentRoutes.derive stopped).isOk
  let helper : Function := ⟨"pending.identity", .math, .privateDef, [.boolean], [.boolean],
    none, [], none, .block [] (.ret [0])⟩
  let callee := (array calls[0]!)[2]!.getStr?.toOption.getD ""
  let pureSnapshot := changeFunctions snapshot fun func =>
    if func.name == callee then { func with body := .block [
      .instruction (.call helper.name) [1] [.boolean] [] "",
      .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [1, 0]) }
    else func
  let pureSnapshot := { pureSnapshot with definitions := pureSnapshot.definitions ++ [.function helper] }
  let pureAdmission := (check pureSnapshot).map (fun _ => ())
  test s!"actual Math route admission: {repr pureAdmission}" pureAdmission.isOk
  test "actual Math route function" ((ComponentRoutes.derive pureSnapshot).toOption.any fun result =>
    result.seams.any (·.kind == .pure))
  IO.println s!"component exports: {← checks.get} checks passed"

private def runStops (snapshot : Snapshot) (text : String) : IO Unit := do
  let program ← expect (check snapshot)
  unless (ZkcTools.SourceClaims.Components.check snapshot text).isOk do
    throw (IO.userError "stopped fixture association")
  for count in [0, 2] do
    let observed ← expect (ZkcTools.StructuredSource.evaluateOpen program (arr [
      .str "zkc.structured-open-request/0", .str "role00000000", arr [.bool false, .str (toString count)],
      arr [], toJson (100000 : Nat)]))
    let status := array ((array observed)[1]?.getD .null)
    unless status[0]? == some (.str "stopped") && status[1]? == some (.str "reject") do
      throw (IO.userError s!"expected actual guard rejection at count={count}")
  IO.println "component stop exports: association and 2 actual rejection cases passed"

private def runVectors (snapshot : Snapshot) (text : String) : IO Unit := do
  let program ← expect (check snapshot)
  unless (ZkcTools.SourceClaims.Components.check snapshot text).isOk do
    throw (IO.userError "vector fixture association")
  for count in [0, 2] do
    for (values, accepted) in [(arr [], true), (arr [.str "3", .str "5"], false)] do
      let observed ← expect (ZkcTools.StructuredSource.evaluateOpen program (arr [
        .str "zkc.structured-open-request/0", .str "role00000000", arr [values, .str (toString count)],
        arr [], toJson (100000 : Nat)]))
      unless (array observed)[1]? == some (arr [.str "returned", arr [.bool accepted]]) do
        throw (IO.userError "vector fixture execution")
  IO.println "component vector exports: association and 4 actual executions passed"

def main (args : List String) : IO Unit := do
  let [snapshotPath, claimsPath, stopSnapshotPath, stopClaimsPath, vectorSnapshotPath, vectorClaimsPath] := args |
    throw (IO.userError "expected ordinary, stopped and vector snapshot/claims paths")
  let snapshot ← Tests.ComponentExports.expect (Format.snapshot (← Tests.ComponentExports.expect
    (Format.parse (← IO.FS.readFile snapshotPath))))
  Tests.ComponentExports.run snapshot (← IO.FS.readFile claimsPath)
  let stopSnapshot ← Tests.ComponentExports.expect (Format.snapshot (← Tests.ComponentExports.expect
    (Format.parse (← IO.FS.readFile stopSnapshotPath))))
  Tests.ComponentExports.runStops stopSnapshot (← IO.FS.readFile stopClaimsPath)
  let vectorSnapshot ← Tests.ComponentExports.expect (Format.snapshot (← Tests.ComponentExports.expect
    (Format.parse (← IO.FS.readFile vectorSnapshotPath))))
  Tests.ComponentExports.runVectors vectorSnapshot (← IO.FS.readFile vectorClaimsPath)

end Tests.ComponentExports
