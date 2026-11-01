module

public import ZkcTools.StructuredSource.Bindings.SourceInstallation

@[expose] public section

/-! A domain-free client: Boolean/index helpers, a dependency decoy, one role,
three returned values, an index capture and two consecutive callback calls.
It uses exactly the same queries and printers as the GKR configuration. -/
namespace Tests.Generators.SourceConfigurations.Counter
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Bindings

def leaf (name : String) : Function := {
  name := name, kind := .local, visibility := .privateDef
  inputs := [.index, .boolean], outputs := [.boolean, .index]
  interface := none, preconditions := [], origin := some (.local name [])
  body := .block [] (.ret [1, 0]) }

def bridge : Function := {
  name := "route", kind := .local, visibility := .privateDef
  inputs := [.boolean, .index, .index], outputs := [.boolean, .index, .index]
  interface := none, preconditions := [], origin := some (.local "route" [])
  body := .block [.instruction (.apply "reorder") [1, 0] [.boolean, .index] [] "reorder"] (.ret [0, 1, 4]) }

def state : List Ty := [.boolean, .index, .index]
def ports (count : Nat) : List (List String) := List.replicate count ["Auditor"]

def child : Function := {
  name := "visit", kind := .protocol, visibility := .publicDef
  inputs := state, outputs := state
  interface := some ⟨["Auditor"], ports 3, ports 3⟩
  preconditions := [], origin := some (.protocol ⟨"counter::Visit", []⟩)
  body := .block [.instruction (.localCall "route" "Auditor") [0, 1, 2] state [] "route"] (.ret [0, 1, 2]) }

def root : Function := {
  name := "counter", kind := .protocol, visibility := .publicDef
  inputs := .index :: (state ++ [.index]), outputs := state
  interface := some ⟨["Auditor"], ports 5, ports 3⟩
  preconditions := [], origin := some (.protocol ⟨"counter::Counter", [("Limit", .natural "5")]⟩)
  body := .block [
    .instruction (.protocolRepeat 3 5 ["Auditor"] (ports 3)) [0, 1, 2, 3, 4] state
      [.region (.index :: (state ++ [.index])) state (.block [
        .instruction (.localCall "route" "Auditor") [1, 2, 3] state [] "prepare",
        .instruction (.protocolApply "visit" ["Auditor"]) [0, 1, 2] state [] "visit",
        .instruction (.protocolApply "visit" ["Auditor"]) [0, 1, 10] state [] "finish"
      ] (.yield [0, 1, 2]))] "passes"
    ] (.ret [0, 1, 2]) }

def snapshot : Snapshot := {
  source := "sha256:" ++ String.ofList (List.replicate 64 '1')
  entry := "counter", domains := [], relations := [], bindings := []
  definitions := [.function (leaf "unused"), .function bridge, .function child,
    .function (leaf "reorder"), .function root]
  contracts := [⟨"visit", []⟩, ⟨"counter", []⟩], catalogue := blsCatalogue }

def configure (program : Program) : Except String SourceInstallation := do
  let childIndex ← uniqueProtocol program ⟨"counter::Visit", []⟩
  let rootIndex ← uniqueProtocol program ⟨"counter::Counter", [("Limit", .natural "5")]⟩
  let some child := program.payload.protocols[childIndex]? | throw "counter-child-index"
  let (callback, site) ← callbackCalling program rootIndex 0 child.signature
  let (bridge, bridgeIndex) ← uniqueHelper program .local state state
  let (_, leafIndex) ← uniqueHelper program .local [.index, .boolean] [.boolean, .index] (some bridge)
  let associations := [("route", bridgeIndex), ("reorder", leafIndex)]
  return {
    protocols := [childIndex, rootIndex]
    templates := { moduleName := "CounterTemplates"
                   namespaceName := "CounterHelpers" }
    namespaceSuffix := "Helpers", associations := associations
    callerSource := fun output => do
      let text := callerSourceHeader output ++ (← helperBodySource program "route" bridgeIndex)
      let text := text ++ (← callbackCallSource program callback site [0] 0 "visit" "passes")
      return text ++ "end\nend " ++ output.moduleName ++ "Caller\n" }

end Tests.Generators.SourceConfigurations.Counter
