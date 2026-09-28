import Tools.Mathematical.PlacementWitness
import Tools.Mathematical.InstallationDescriptors

/-! Check the actual common target against independently derived role demand.

The witness chooses spelling. Every scope, alias, operation package, root,
effect position and result incidence is reconstructed from the admitted body.
Pure site labels are metadata and are read from the actual target; common
admission subsequently checks their grammar and uniqueness.
-/

set_option autoImplicit false
namespace Tools.Mathematical.PlacementCheck
open Zkc.Source.Mathematical BlsInstallation
open PlacementGraph (Body Component)
open PlacementWitness (Witness Target)

private def strings (values : List String) : Raw.Attribute := .array (values.map .string)
private def list (value : Raw.Attribute) := PlacementWitness.array value

structure State where
  remaining : Nat
  bindings : List Raw.Attribute := []
  operations : List Nat := []
  wires : List Nat := []
  sites : List Nat := []

abbrev Check := StateT State (Except String)

def ensure (ok : Bool) (code : String) : Check Unit :=
  if ok then pure () else throw code

private def consume (amount : Nat := 1) : Check Unit := do
  let state ← get
  ensure (amount ≤ state.remaining) "math-placement-resource"
  set {state with remaining := state.remaining - amount}

private def select {α : Type} (values : List α) (index : Nat) : Check α := do
  consume (1 + values.length)
  match values[index]? with
  | some value => return value
  | none => throw "math-placement-target-scope"

private def mapping (values : List (Nat × String)) (index : Nat) : Check String := do
  consume (1 + values.length)
  match values.find? (·.1 == index) with
  | some value => return value.2
  | none => throw "math-placement-witness-coverage"

private def vertex (body : Body) (index : Nat) : Check PlacementGraph.Vertex := do
  consume
  match body.vertices[index]? with
  | some value => return value
  | none => throw "math-placement-source-scope"

private def role (source : Raw.Subject) (index : Nat) : Check String := select source.module.roles index

private def component (body : Body) (witness : Witness) (index owner : Nat) (scope : List Nat := []) : Check String := do
  let value ← vertex body index
  consume (1 + witness.components.length)
  let some mapping := witness.components.find? (fun c => c.source == value.address && c.role == owner)
    | throw "math-placement-witness-coverage"
  ensure (mapping.target.regions == scope) "math-placement-component-scope"
  return mapping.target.name

private def live (demand : List Component) (index owner : Nat) : Check Bool := do
  consume (1 + demand.length)
  return demand.contains (index, owner)

private def spelling (body : Body) (index : Nat) : Check String := do
  return InstallationDescriptors.spelling (← vertex body index).port.type

private def binding (name : String) (selected : String × List String) : Check Unit := do
  let value := Raw.Attribute.array [.string name, .string selected.1, strings selected.2, .string ""]
  consume (1 + (← get).bindings.length)
  if !(← get).bindings.contains value then
    modify fun state => {state with bindings := state.bindings ++ [value]}

private def site (witness : Witness) (index : Nat) (kind : String) : Check String := do
  consume (1 + witness.sites.length)
  let some selected := witness.sites.find? (·.site == index) | throw "math-placement-site-coverage"
  ensure (selected.kind == kind && !(← get).sites.contains index) "math-placement-site-kind"
  modify fun state => {state with sites := state.sites ++ [index]}
  return selected.target

private def pureRegion (source : Raw.Subject) (body : Body) (demand : List Component)
    (witness : Witness) (owner position : Nat) (captures : List Nat)
    (nodes : List PlacementGraph.Node) (outputs : List Nat) (actual : Raw.Attribute) : Check Raw.Attribute := do
  let [.string "pure", label, _, _, actualNodes, _] ← list actual | throw "math-placement-pure"
  let actualNodes ← list actualNodes
  let scope := [position, 0]
  let mut inputPorts := []
  for input in captures do
    if ← live demand input owner then
      let name ← component body witness input owner scope
      let [outer] := (← vertex body input).dependencies | throw "math-placement-capture"
      ensure (name == (← component body witness outer owner)) "math-placement-capture-alias"
      let port := Raw.Attribute.array [.string name, .string (← spelling body input)]
      consume (1 + inputPorts.length)
      if !inputPorts.contains port then inputPorts := inputPorts ++ [port]
  let mut code := []
  for node in nodes do
    if ← live demand node.output owner then
      let [.string "op", nodeLabel, _, _, _, _] ← list (← select actualNodes code.length)
        | throw "math-placement-pure-operation"
      let operation ← mapping witness.operations node.declaration
      binding operation (InstallationDescriptors.operationBinding node.operation)
      if !(← get).operations.contains node.declaration then
        modify fun state => {state with operations := state.operations ++ [node.declaration]}
      let inputs ← node.arguments.mapM fun index => component body witness index owner scope
      let output ← component body witness node.output owner scope
      code := code ++ [.array [.string "op", nodeLabel, .string operation, .array [], strings inputs, strings [output]]]
  let mut outputPorts := []
  let mut yields := []
  for output in outputs do
    if ← live demand output owner then
      outputPorts := outputPorts ++ [.array [.string (← component body witness output owner),
        .string (← spelling body output)]]
      let [internal] := (← vertex body output).dependencies | throw "math-placement-yield"
      yields := yields ++ [← component body witness internal owner scope]
  code := code ++ [.array [.string "yield", strings yields]]
  return .array [.string "pure", label, .string (← role source owner), .array inputPorts, .array code, .array outputPorts]

private def stopReason : PIR.Stop → String
  | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted"
  | .incomplete => "incomplete" | .refused => "refused"

private def instructions (source : Raw.Subject) (body : Body) (demand : List Component)
    (witness : Witness) (actual : List Raw.Attribute) : Check (List Raw.Attribute) := do
  let mut expected := []
  for step in body.steps do
    consume (1 + expected.length)
    match step with
    | .pure _ captures nodes outputs =>
        for owner in List.range source.module.roles.length do
          let used ← outputs.anyM (fun output => live demand output owner)
          if used then
            let placed ← pureRegion source body demand witness owner expected.length captures nodes outputs
              (← select actual expected.length)
            expected := expected ++ [placed]
    | .query index owner root output =>
        expected := expected ++ [.array [.string "query", .string (← site witness index "query"),
          .string (← role source owner), .string (← mapping witness.roots root), .array [],
          strings [← component body witness output owner]]]
    | .guard index owner condition =>
        expected := expected ++ [.array [.string "guard", .string (← site witness index "guard"),
          .string (← role source owner), .string (← component body witness condition owner)]]
    | .message index wire sender receiver input output =>
        let schema ← mapping witness.wires wire
        if !(← get).wires.contains wire then
          modify fun state => {state with wires := state.wires ++ [wire]}
        let sent ← component body witness input sender
        ensure ((← component body witness output sender) == sent) "math-placement-sender-alias"
        expected := expected ++ [.array [.string "message", .string (← site witness index "message"),
          .string schema, .string (← role source sender), .string (← role source receiver),
          .string sent, .string (← component body witness output receiver)]]
  match body.terminal with
  | .stop index owner reason =>
      expected := expected ++ [.array [.string "stop", .string (← site witness index "stop"),
        .string (← role source owner), .string (stopReason reason)]]
  | .ret values =>
      let mut returns := []
      for owner in List.range source.module.roles.length do
        for (value, result) in values.zip body.results do
          if result.roles.contains owner then
            returns := returns ++ [← component body witness value owner]
      expected := expected ++ [.array [.string "return", strings returns]]
  return expected

private def results (source : Raw.Subject) (body : Body) (witness : Witness) : Check Raw.Attribute := do
  let mut ports := []
  let mut mappings := []
  for owner in List.range source.module.roles.length do
    let mut position := 0
    for (result, index) in body.results.zipIdx do
      if result.roles.contains owner then
        ports := ports ++ [strings [← role source owner, InstallationDescriptors.spelling result.type]]
        mappings := mappings ++ [PlacementWitness.Result.mk owner index position]
        position := position + 1
  ensure (mappings == witness.results) "math-placement-result-mapping"
  return .array ports

private def roots {source : Raw.Subject} (header : DeclarationAdmission.Header BlsAdmission.installed source)
    (witness : Witness) (actual : List Raw.Attribute) : Check (List Raw.Attribute) := do
  ensure (actual.length == header.capabilities.length && witness.roots.length == actual.length)
    "math-placement-root-coverage"
  let mut roots := []
  for (root, index) in header.capabilities.zipIdx do
    let [.string "root", _, .string serviceName, _] ← list (← select actual index) | throw "math-placement-root"
    let service ← if root.service.val.identity == Service.draw.identity then pure Service.draw
      else if root.service.val.identity == Service.drawNonzero.identity then pure Service.drawNonzero
      else throw "math-placement-service"
    binding serviceName (InstallationDescriptors.serviceBinding service)
    let owners ← root.roles.mapM (role source)
    roots := roots ++ [.array [.string "root", .string (← mapping witness.roots index),
      .string serviceName, strings (owners.mergeSort (· ≤ ·))]]
  return roots

def check {source : Raw.Subject} (header : DeclarationAdmission.Header BlsAdmission.installed source)
    (body : Body) (demand : List Component) (witness : Witness) (actual : Raw.Attribute) : Check Unit := do
  ensure (body.key == witness.key && body.key == ClosedInstances.entryKey source) "math-placement-instance-key"
  ensure (demand.length == witness.components.length) "math-placement-demand-coverage"
  for (value, owner) in demand do
    let address := (← vertex body value).address
    consume (1 + witness.components.length)
    ensure (witness.components.any (fun c => c.source == address && c.role == owner)) "math-placement-demand-coverage"
  let fields ← list actual
  let (bindings, protocols, _instances, entries, actualRoots, hasRoots) ← match fields with
    | [.string "zkc.protocol/1", bindings, .array [], protocols, instances, entries] =>
        pure (bindings, protocols, instances, entries, Raw.Attribute.array [], false)
    | [.string "zkc.protocol/1", bindings, .array [], protocols, instances, entries, roots] =>
        pure (bindings, protocols, instances, entries, roots, true)
    | _ => throw "math-placement-module"
  let [protocol] ← list protocols | throw "math-placement-protocol"
  let [.string "protocol", _, _, .array [], _, _, .array [], actualBody] ← list protocol
    | throw "math-placement-protocol"
  let [entry] ← list entries | throw "math-placement-entry"
  let [.string "entry", entryName, _] ← list entry | throw "math-placement-entry"
  let roots ← roots header witness (← list actualRoots)
  let mut arguments := []
  for owner in List.range source.module.roles.length do
    for input in body.arguments do
      if ← live demand input owner then
        arguments := arguments ++ [strings [← component body witness input owner,
          ← role source owner, ← spelling body input]]
  let code ← instructions source body demand witness (← list actualBody)
  let resultPorts ← results source body witness
  -- Availability uses canonical role sets; the protocol interface retains the
  -- authored positional binding. Both are already module-role coordinates.
  let parties ← body.key.roles.mapM (role source)
  let expectedProtocol := Raw.Attribute.array [.string "protocol", .string witness.protocol, strings parties,
    .array [], .array arguments, resultPorts, .array [], .array code]
  let expectedInstance := Raw.Attribute.array [.string "instance", .string witness.instanceName,
    .string witness.protocol, .array [], .array [], .array (parties.map fun name => strings [name, name])]
  let expectedEntry := Raw.Attribute.array [.string "entry", entryName, .string witness.instanceName]
  for ((actualField, expectedField), index) in ((← list protocol).zip (← list expectedProtocol)).zipIdx do
    ensure (actualField == expectedField) ("math-placement-protocol-field-" ++ toString index)
  let state ← get
  ensure (state.operations.length == witness.operations.length && state.wires.length == witness.wires.length &&
    state.sites.length == witness.sites.length) "math-placement-witness-coverage"
  -- Declaration order is not semantic. Each complete binding must occur once.
  let actualBindings ← list bindings
  consume (1 + actualBindings.length * (state.bindings.length + 1))
  ensure (actualBindings.length == state.bindings.length &&
    state.bindings.all (fun value => actualBindings.contains value)) "math-placement-bindings"
  let fields := [.string "zkc.protocol/1", bindings, .array [], .array [expectedProtocol],
    .array [expectedInstance], .array [expectedEntry]]
  let expected := Raw.Attribute.array (if hasRoots then fields ++ [.array roots] else fields)
  ensure (actual == expected) "math-placement-correspondence"

end Tools.Mathematical.PlacementCheck
