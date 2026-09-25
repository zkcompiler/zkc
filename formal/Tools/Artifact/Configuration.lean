import Tools.Artifact.Descriptor

/-! Application setup authorization reconstructed from original source ports.
Executable receive coverage excludes exact zero-trip bodies. Runtime proof bytes
never choose the selected key. Full curve/key validity remains an external
public-cryptography contract; metadata and coverage are checked here. -/

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

abbrev ReceiveSite := Name × Name × Name

/-- Exact application selection; a missing coordinate cannot use wire metadata. -/
def selection {α : Type} [BEq α] (coordinate : α) (choices : List (α × Name)) : Result Name := do
  let some (_, name) := choices.find? (fun p => p.1 == coordinate) | throw "artifact-setup-selection"
  return name

/-- Setup selection belongs to the installed KZG scheme, not to the spelling
`proof` or `commitment`. Transparent row authentication has no setup key. -/
def requiresSetup (ty : Ty) : Bool :=
  let kind := typeKind ty
  (kind == "commitment" || kind == "proof") &&
    (ty == kind || ty == kind ++ ":" ++ Bindings.pcs)

private def receiveBody (source : Source) (binding : Instance) (definition : Protocol) :
    Nat → Context → List Instruction → Result (List ReceiveSite × List Name)
  | 0, _, _ => .error "configuration-body-depth"
  | fuel + 1, initial, body => do
      let mut context := initial
      let mut sites := []
      let mut children := []
      for instruction in body do
        match instruction with
        | .localCall _ owner function _ outputs =>
            let owner ← binding.role owner
            let function ← source.function function
            context ← context.bind outputs (function.results.map (owner, ·))
        | .message site _ _ receiver input output =>
            let receiver ← binding.role receiver
            let ty := (← context.get input).ty
            if requiresSetup ty then sites := (binding.name, receiver, site) :: sites
            context ← context.bind [output] [(receiver, ty)]
        | .call _ dependency _ outputs =>
            let (_, results) ← callSignature source definition (some binding) dependency
            children := (← lookup dependency binding.dependencies) :: children
            context ← context.bind outputs results
        | .loop _ count carried captures body outputs =>
            let carriedPorts ← context.read (carried.map Prod.snd)
            let ports := carriedPorts.map (fun p => (p.owner, p.ty))
            let captured ← context.read captures
            let inner ← Context.bind [] (carried.map Prod.fst) ports
            let inner ← inner.bind captures (captured.map (fun p => (p.owner, p.ty)))
            if (← binding.count count) > 0 then
              let (nested, dependencies) ← receiveBody source binding definition fuel inner body
              sites := nested ++ sites
              children := dependencies ++ children
            context ← context.bind outputs ports
        | .ret _ | .yield _ | .stop .. => pure ()
        | _ => throw "configuration-common-body"
      return (sites, children)

def receiveSites (source : Source) (root : Instance) : Result (List ReceiveSite) := do
  let mut pending := [root.name]
  let mut visited := []
  let mut sites := []
  for _ in [:source.instances.length + 1] do
    let some name := pending.head? | break
    pending := pending.drop 1
    if !visited.contains name then
      visited := name :: visited
      let binding ← source.binding name
      let definition ← source.protocol binding.protocol
      let some body := definition.body | throw "external-protocol"
      let ports ← definition.arguments.mapM fun p => return (← binding.role p.owner, p.ty)
      let context ← Context.bind [] (definition.arguments.map Port.name) ports
      let (found, children) ← receiveBody source binding definition limits.callDepth context body
      sites := found ++ sites
      pending := (children ++ pending).eraseDups.filter (fun n => !visited.contains n)
  ensure pending.isEmpty "configuration-instance-limit"
  return sites.eraseDups

structure SetupConfiguration where
  keys : List (Name × Value)
  inputs : List ((Name × Name) × Name) := []
  receives : List (ReceiveSite × Name) := []

def decodeConfiguration (source : Source) (descriptor : Descriptor) (binding : Instance)
    (definition : Protocol) (json : Json) : Result SetupConfiguration := do
  let record ← Decode.array json
  let (records, inputJson, receiveJson) ← match record with
    | [.str "zkc.public-configuration/1", records, inputs, receives] => pure (records, inputs, receives)
    | _ => throw "public-configuration"
  let ports ← definition.arguments.filterM fun p =>
    return (← binding.role p.owner) == descriptor.validator && typeKind p.ty == "verifier_key"
  let records ← Decode.array records limits.ports
  ensure (records.length == ports.length) "configuration-coverage-or-order"
  let mut keys := []
  let mut material : List ByteArray := []
  for (record, port) in records.zip ports do
    let [.str name, .str ty, .str wire] ← Decode.array record | throw "configuration-key-record"
    ensure (name == port.name && ty == port.ty) "configuration-coverage-or-order"
    let bytes ← unhex wire
    let key ← decodeValue ty bytes
    for other in material do
      ensure (bytes == other || bytes.extract 9 81 != other.extract 9 81)
        "artifact-conflicting-verifier-keys"
    material := (bytes :: material).eraseDups
    ensure (material.length ≤ 64) "artifact-setup-count"
    keys := keys ++ [(name, key)]
  let mut inputs := []
  let mut receives := []
  let mut expected ← (definition.arguments.filter (fun p => requiresSetup p.ty)).mapM fun p =>
    return (← binding.role p.owner, p.name)
  for row in ← Decode.array inputJson limits.ports do
    let [role, port, key] ← Decode.array row | throw "artifact-input-setup-record"
    let coordinate := (← Decode.name role, ← Decode.name port)
    ensure (expected.contains coordinate) "artifact-input-setup-port-or-duplicate"
    expected := expected.erase coordinate
    let key ← Decode.name key
    let _ ← lookup key keys
    inputs := (coordinate, key) :: inputs
  ensure expected.isEmpty "artifact-input-setup-coverage"
  let mut expectedReceives := (← receiveSites source binding).filter (fun s => s.2.1 == descriptor.validator)
  for row in ← Decode.array receiveJson do
    let [bindingName, role, site, key] ← Decode.array row | throw "artifact-receive-record"
    let coordinate := (← Decode.name bindingName, ← Decode.name role, ← Decode.name site)
    ensure (expectedReceives.contains coordinate) "artifact-receive-site-or-duplicate"
    expectedReceives := expectedReceives.erase coordinate
    let key ← Decode.name key
    let _ ← lookup key keys
    receives := (coordinate, key) :: receives
  ensure expectedReceives.isEmpty "artifact-receive-coverage"
  return ⟨keys, inputs, receives⟩

/-- Only the application-selected key can authorize a PCS input or receive. -/
def checkSetup (configuration : SetupConfiguration) (selected : Name) (value : Value) : Result Unit := do
  let .verifierKey key ← lookup selected configuration.keys | throw "configuration-key-type"
  let wire ← value.wire
  ensure (requiresSetup (← value.typeFor) && wire.extract 15 87 == key.extract 9 81) "key-mismatch"

end Tools.Artifact
