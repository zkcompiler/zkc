module

public import ZkcTools.StructuredSource.Discovery.Json

@[expose] public section

/-! The measured explicit-descriptor baseline. This module is not imported by
Search and its data is never an input to either automatic proposer. -/

namespace ZkcTools.StructuredSource.Discovery
open Lean Zkc.Source Zkc.Source.Structured

def manualRequest (view : View) (json : Json) : Except String Outcome := do
  let .arr requests := json | throw "discovery-manual-shape"
  let candidates : List Candidate ← requests.toList.mapM fun request => do
    let .arr #[loopIndex, .str templateText, stateIndices, updateIndices] := request
      | throw "discovery-manual-shape"
    let loopIndex : Nat ← fromJson? loopIndex
    let stateIndices : List Nat ← fromJson? stateIndices
    let updateIndices : List Nat ← fromJson? updateIndices
    let template ← match templateText with
      | "table" => pure Template.table | "factors" => pure Template.factors
      | _ => throw "discovery-manual-template"
    let some loop := (view.nodes.filter (·.tag == "repeat"))[loopIndex]?
      | throw "discovery-manual-loop"
    let nodes := view.nodes.filter fun node => node.address.definition == loop.address.definition &&
      node.context == loop.context && (loop.address.region ++ [2, 0]).isPrefixOf node.address.region
    let state ← stateIndices.mapM fun index => do
      let some value := loop.arguments[index]? | throw "discovery-manual-state"
      match value.type with
      | .vector _ => pure value.address
      | _ => throw "discovery-manual-state"
    let helpers := nodes.filter (·.tag == "local-helper")
    let updates ← updateIndices.mapM fun index => do
      let some helper := helpers[index]? | throw "discovery-manual-update"
      pure helper.address
    let messages := nodes.filter fun node => node.tag == "receive" &&
      node.roleMap[1]? == some node.selectedRole
    if state.isEmpty || messages.isEmpty || updates.isEmpty then throw "discovery-manual-empty"
    return {       template, occurrence := loop.address, context := loop.context, state,       message := messages.flatMap fun node => node.results.map (·.address), updates,       helpers := helpers.filterMap (·.helper), degree := if template == .table then 1 else 2,       obligations := commonObligations ++ (if template == .factors then         ["separate-factor-representation", "active-variable-independent-weight",          "off-cube-observation-preservation", "reference-degree-at-most-two"] else         ["table-representation", "affine-message-representation"]) }
  pure (manual candidates)

end ZkcTools.StructuredSource.Discovery
