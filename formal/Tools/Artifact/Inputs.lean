import Tools.Artifact.Interpreter
import Tools.Artifact.Identity

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

structure Invocation where
  source : Source
  descriptor : Descriptor
  binding : Instance
  definition : Protocol
  context : Context
  environment : Environment
  publicValues : List Value
  root : ByteArray
  configuration : Json
  setups : SetupConfiguration

def inputValue (ty : Ty) (encoded : String)  : Result Value := do
  decodeValue ty (← unhex encoded)

def valueRecords (json : Json) (labels : Bool := false)  : Result (List (Name × Value)) := do
  let records ← (← Decode.array json limits.ports).mapM fun record => do
    let [name, .str ty, .str encoded] ← Decode.array record | throw "input-value-record"
    let name ← if labels then bindingLabel name else Decode.name name
    return (name, ← inputValue ty encoded)
  ensure (unique (records.map Prod.fst)) "duplicate-input-record"
  return records

def prepare (sourceJson descriptorJson inputs : Json) : Result Invocation := do
  let identity ← if Identity.selected descriptorJson then
      some <$> Identity.prepare sourceJson descriptorJson
    else pure none
  let source ← match identity with
    | some identity => pure identity.resolvedSource
    | none => artifactSource sourceJson
  let descriptor ← match identity with
    | some identity => pure identity.descriptor
    | none => decodeDescriptor source descriptorJson (← artifactOrigins sourceJson)
  admitArtifactProfile source descriptor
  let binding ← source.binding (← lookup descriptor.entry source.entries)
  let definition ← source.protocol binding.protocol
  let ports ← definition.arguments.mapM fun p => return (← binding.role p.owner, p.ty)
  let context ← Context.bind [] (definition.arguments.map Port.name) ports
  let [.str tag, .str applicationContext, publicJson, inputJson, configJson] ← Decode.array inputs
    | throw "artifact-inputs"
  ensure (tag == "zkc.artifact-inputs/1") "artifact-inputs"
  let configJson ← match identity with
    | some identity => identity.configuration configJson
    | none => pure configJson
  let _ ← unhex applicationContext
  let publicValues ← valueRecords publicJson true
  ensure (publicValues.length == descriptor.publicBindings.length &&
    descriptor.publicBindings.all (fun p => publicValues.any (fun v => v.1 == p.label))) "public-input-coverage"
  let setups ← decodeConfiguration source descriptor binding definition configJson
  let configValues := setups.keys
  let mut supplied ← valueRecords inputJson false
  let ownPorts := context.filter fun p => p.owner == descriptor.validator
  let expected := ownPorts.filter fun p => p.name != descriptor.rng
  for p in expected do
    let configured ← if typeKind p.ty == "verifier_key" then
        some <$> lookup p.name configValues
      else match descriptor.publicBindings.find? (fun b => b.ports.contains (descriptor.validator, p.name)) with
        | none => pure none
        | some binding => some <$> lookup binding.label publicValues
    if let some value := configured then
      match supplied.find? (fun item => item.1 == p.name) with
      | none => supplied := supplied ++ [(p.name, value)]
      | some (_, actual) => ensure ((← actual.json) == (← value.json)) "configured-input-agreement"
  let suppliedTypes ← supplied.mapM fun (name, value) => return (name, ← value.typeFor)
  ensure (supplied.length == expected.length && expected.all (fun p =>
    suppliedTypes.contains (p.name, p.ty))) "source-input-coverage"
  let mut environment := supplied
  environment ← bind environment [descriptor.rng]
    [if descriptor.suite == Bindings.extensionTranscript then .extensionRng 0 else if descriptor.suite == Bindings.ristrettoTranscript then .ristrettoRng 0 else .selectedRng 0]
  let mut publicRecords : Array Json := #[]
  for declaration in descriptor.publicBindings do
    let value ← lookup declaration.label publicValues
    let some (_, sourcePort) := declaration.ports.head? | throw "public-empty-binding"
    let declared ← context.get sourcePort
    ensure (declared.ty == (← value.typeFor)) "public-input-type"
    let wire ← value.wire
    for (role, name) in declaration.ports do
      let declared ← context.get name
      ensure (declared.owner == role && declared.ty == (← value.typeFor)) "public-input-type"
      if requiresSetup (← value.typeFor) then
        let selected ← selection (role, name) setups.inputs
        checkSetup setups selected value
      if role == descriptor.validator then
        let actual ← lookup name environment
        ensure ((← actual.wire) == wire) "public-input-agreement"
    let ty ← Json.str <$> value.typeFor
    publicRecords := publicRecords.push (.arr #[.str declaration.label, ty, .str (hex wire)])
  let rootJson := match identity with
    | some identity => Json.arr #[.str "zkc.artifact-binding/1", identity.normalized,
        descriptor.json, .str applicationContext, .arr publicRecords, configJson]
    | none => Json.arr #[.str "zkc.artifact-binding/1",
        sourceJson, descriptorJson, .str applicationContext, .arr publicRecords, configJson]
  -- Input records are keyed by label, while runtime setup validation pairs
  -- these values with declarations. Retain declaration order in both lists.
  let orderedPublic ← descriptor.publicBindings.mapM fun declaration =>
    lookup declaration.label publicValues
  return ⟨source, descriptor, binding, definition, context, environment,
    orderedPublic, ← treeBytes rootJson, configJson, setups⟩

def decodeAnswers (json : Json) : Result (Array OracleReply) := do
  let [.str "zkc.primitive-replies/1", records] ← Decode.array json | throw "primitive-replies"
  let mut answers : Array OracleReply := #[]
  for record in ← Decode.array records do
    let [request, response] ← Decode.array record | throw "primitive-reply"
    ensure (!(answers.any fun a => a.request == request)) "duplicate-primitive-request"
    answers := answers.push ⟨request, response⟩
  return answers

def run (invocation : Invocation) : RunM (List Value) := do
  let source := invocation.source
  -- Validate the entire application key registry before proof processing.
  for (_, value) in invocation.setups.keys do validatePublic source value
  for (name, value) in invocation.environment do
    if value.ty != "rng" then
      let selected ← if requiresSetup (← checked (value.typeFor)) then
          some <$> checked (selection (invocation.descriptor.validator, name) invocation.setups.inputs)
        else pure none
      validatePublic source value selected
  for (declaration, value) in invocation.descriptor.publicBindings.zip invocation.publicValues do
    let selected ← if requiresSetup (← checked (value.typeFor)) then do
        let some coordinate := declaration.ports.head? | fail "refused" "public-empty-binding"
        some <$> checked (selection coordinate invocation.setups.inputs)
      else pure none
    validatePublic source value selected
  let header ← oracle (.arr #[.str "zkc.hash/1", .str "sha256", .str (hex invocation.root)])
  let expected ← checked (unhex (← checked (Decode.string header)))
  require (expected.size == 32) "hash-response"
  let (header, cursor) ← checked ((← get).cursor.read 40)
  modify fun s => { s with cursor := cursor }
  require (header.extract 0 8 == "ZKCPRF01".toUTF8 && header.extract 8 40 == expected) "proof-header"
  let some body := invocation.definition.body | fail "refused" "external-protocol"
  let location : Location := {
    entry := invocation.descriptor.entry
    binding := invocation.binding.name
    path := []
    protocol := invocation.definition.name
    role := invocation.descriptor.validator }
  let outputs ← execute invocation.source invocation.descriptor limits.callDepth
    invocation.binding invocation.definition location invocation.context invocation.environment body
  require (← get).cursor.finished "proof-trailing"
  let some (.boolean accepted) := outputs[invocation.descriptor.acceptance]?
    | fail "refused" "acceptance-output"
  if !accepted then fail "reject" "acceptance-false"
  let state ← get
  require (state.usedAnswers.eraseDups.length == state.answers.size) "unused-primitive-replies"
  return outputs

end Tools.Artifact
