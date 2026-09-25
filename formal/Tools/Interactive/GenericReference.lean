import Tools.Interactive.GenericModule
import Tools.Interactive.ReferenceControl
import Tools.Interactive.ReferenceAdmission
import Tools.Interactive.ReferenceSetups

/-! Original generic source reference, independent of native participants.

The host fixture supplies original port names, finite random services and exact
external requests. Whole-source formation and independent source specialization
precede input admission. Runtime evidence is scoped to implemented logical
services, not physical allocation or native elaborator adequacy.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference
open Lean (Json)

structure Invocation where
  location : Location
  binding : Instance
  definition : Protocol
  context : Context
  environments : Control.RoleEnvironments Value
  state : State

/-- A host session identifier is not a source symbol. The native runner accepts
ASCII digits and punctuation at its start, with a 128-byte bound. -/
def decodeSession (json : Json) : Result String := do
  let value ← Decode.string json
  ensure (!value.isEmpty && value.utf8ByteSize ≤ 128 &&
    value.toList.all (fun c => Decode.asciiLetter c || Decode.asciiDigit c ||
      c == '_' || c == '.' || c == '-')) "invalid-session"
  return value

private def decodeResource (json : Json) : Result Resource := do
  let [identity, owner, boundInstance, budget, initializer] ← Decode.array json | throw "reference-resource"
  let boundInstance ← if boundInstance == .arr #[] then pure none else do pure (some (← Decode.name boundInstance))
  let budget ← Decode.natural budget
  ensure (budget ≤ 18446744073709551615) "resource-budget-limit"
  let [.str kind, value] ← Decode.array initializer | throw "resource-initializer"
  let payload : ResourcePayload ← match kind with
    | "rng:koala-bear.ext8-binomial3" => do
        let tape ← (← Decode.array value 1048576).mapM fun item => do
          let [.str kind, payload] ← Decode.array item | throw "extension-rng-tape"
          if kind == "index" then
            let n ← Decode.natural payload
            ensure (n < 2^64) "extension-rng-tape"
            pure (ScalarReference.Data.index n : ExtensionReference.Data)
          else
            ensure (kind == "field") "extension-rng-tape"
            pure (ScalarReference.Data.field (← ExtensionReference.scalar payload) : ExtensionReference.Data)
        pure (.erng tape)
    | "transcript:merlin3.koala-bear.ext8-binomial3.rejection31le/1" => do
        pure (.transcript Bindings.extensionTranscript (← Tools.Artifact.treeBytes value) #[])
    | "rng:bn254.fr" => do pure (.brng (← (← Decode.array value 1048576).mapM (ScalarReference.decodeScalar .bn254)))
    | "rng:ristretto255.scalar" => do pure (.rrng (← (← Decode.array value 1048576).mapM (ScalarReference.decodeScalar .ristretto)))
    | "nonce:ristretto255.scalar" => do pure (.rnonce (.issued (← ScalarReference.decodeScalar .ristretto value)))
    | "transcript:merlin3.ristretto255.scalar64le/1" => do pure (.transcript Bindings.ristrettoTranscript (← Tools.Artifact.treeBytes value) #[])
    | "rng" => do pure (.rng (← decodeScalars value))
    | "nonce" => do pure (.nonce (.issued (← decodeScalar value)))
    | "transcript:spongefish0.7.4.keccak.bls12-381.fr64be/1" => do pure (.transcript Bindings.spongefishTranscript (← Tools.Artifact.treeBytes value) #[])
    | "transcript" => do pure (.transcript Bindings.transcriptIdentity (← Tools.Artifact.treeBytes value) #[])
    | _ => throw "resource-kind"
  return ⟨← Decode.name identity, ← Decode.name owner, boundInstance, budget, payload, 0, 0⟩

private def records (json : Json) : Result (List (Json × Json)) := do
  let mut seen : Std.HashSet String := {}
  let mut records := []
  for row in ← Decode.array json do
    let [request, response] ← Decode.array row | throw "reference-service-record"
    let key := request.compress
    ensure (!(seen.contains key)) "duplicate-reference-request"
    seen := seen.insert key
    records := (request, response) :: records
  return records.reverse

def invocation (prepared : Generic.Prepared) (selected : Option Name) (json : Json) : Result Invocation := do
  let parts ← Decode.array json
  let (parts, setups) := if parts.length == 8 then (parts.take 7, parts[7]!) else (parts, .arr #[])
  let [.str "zkc.reference-inputs/1", entry, session, supplied, resources, answers, replies] := parts
    | throw "reference-inputs"
  let entry ← Decode.name entry
  let session ← decodeSession session
  let source := prepared.source
  let binding ← source.binding (← lookup entry source.entries)
  let definition ← source.protocol binding.protocol
  if let some role := selected then ensure ((binding.roles.map Prod.snd).contains role) "unknown-role"
  let roles := (binding.roles.map Prod.snd).filter (Control.active selected)
  let resources ← (← Decode.array resources).mapM decodeResource
  ensure (unique (resources.map Resource.identity)) "duplicate-resource"
  ensure (resources.all (fun r => roles.contains r.owner &&
    r.boundInstance.all (fun name => source.instances.any (·.name == name)))) "resource-domain"
  let answers := Std.HashMap.ofList ((← records answers).map fun (request, response) => (request.compress, response))
  let replies ← (← records replies).mapM fun (request, response) => do
    let value ← decodeValue response
    ensure value.public "nonserializable-reply"
    return (request, value)
  let (setupKeys, receivingKeys) ← setupContext roles setups
  let state : State := { resources, answers, replies, setupKeys, receivingKeys }
  let supplied ← Decode.pairs Decode.name (Decode.pairs Decode.name decodeValue) supplied
  ensure (exactKeys supplied (roles.map fun r => (r, ()))) "input-roles"
  let context ← definition.arguments.mapM fun p => return { p with owner := ← binding.role p.owner }
  let mut environments := roles.map fun role => (role, [])
  let mut used := []
  for role in roles do
    let ports := context.filter (·.owner == role)
    let values ← lookup role supplied
    ensure (exactKeys values (ports.map fun p => (p.name, ()))) "input-ports"
    for port in ports do
      let value ← lookup port.name values
      authorized state role value
      if let some (kind, identity, generation) := value.capability then
        let resource ← lookup identity (resources.map fun r => (r.identity, r))
        ensure (resource.payload.kind == kind) "capability-kind"
        ensure (resource.payload.domain == value.ty.identity) "capability-identity"
        ensure (resource.owner == role && resource.boundInstance.all (· == binding.name)) "capability-domain"
        ensure (generation == 0) "capability-stale"
        ensure (!(used.contains identity)) "capability-alias"
        used := identity :: used
      environments ← Control.bindPorts (fun v => v.ty.spelling) selected environments
        [port.name] [(role, port.ty)] [value]
  let location : Location := ⟨session, entry, ⟨binding.name, [], "entry", selected.getD "joint"⟩, none, #[]⟩
  return ⟨location, binding, definition, context, environments, state⟩

def receiveKey (location : Location) (schema peer : Name) (ty : Ty) : Json :=
  .arr #[.str "receive", location.json, .str schema, .str peer, .str ty]

private def services (prepared : Generic.Prepared) (base : Location) : Control.Services Value RunM where
  typeOf value := value.ty.spelling
  fail scope reason detail := do
    activateRole scope.role
    failAt { base with scope } reason detail
  charge scope := charge { base with scope }
  iteration scope := do
    let location := { base with scope }
    if (← get).iterations ≥ 100000 then failAt location "exhausted" "local-iteration-limit"
    modify fun state => { state with iterations := state.iterations + 1 }
  executeLocal scope function inputs := do
    let location := { base with scope }
    activateRole scope.role
    recordBoundary location inputs
    activateRole scope.role
    let some typed := prepared.typedFunctions.find? (·.name == function.name)
      | failAt location "refused" "missing-typed-source-function"
    let path ← checked location (interactionPath prepared.source location)
    let values ← executeFunction { location with interactionPath := path } typed inputs
    recordBoundary location values
    activateRole scope.role
    return values
  send scope schema receiver value := do
    let location := { base with scope }
    activateRole scope.role
    validatePublic location value
    event location (.arr #[.str "send", location.json, .str schema, .str receiver, value.json]) (1 + value.size)
  received scope schema sender value := do
    let location := { base with scope }
    activateRole scope.role
    validateReceivingKey location (receiveKey location schema sender value.ty.spelling) value
    event location (.arr #[.str "receive", location.json, .str schema, .str sender, value.json]) (1 + value.size)
  receive scope schema peer ty := do
    let location := { base with scope }
    activateRole scope.role
    let state ← get
    let (request, value) :: rest := state.replies | failAt location "pending" "message-reply-missing"
    require location (request == receiveKey location schema peer ty) "reply-origin"
    require location (value.ty.spelling == ty) "reply-type"
    validateReceivingKey location request value
    validatePublic location value
    modify fun state => { state with replies := rest }
    event location (.arr #[.str "receive", location.json, .str schema, .str peer, value.json]) (1 + value.size)
    return value
  enterRegion scope environments := do
    for (role, store) in environments do
      recordBoundary { base with scope := { scope with role } } (store.map Prod.snd)
  exitRegion scope values := do
    for role in (values.map Prod.fst).eraseDups do
      recordBoundary { base with scope := { scope with role } }
        ((values.filter (fun pair => pair.1 == role)).map Prod.snd)

/-- Entry validation and ingress run before any participant can return. On a
failure their root units are therefore cancelled, independently of later host
fixture checks. Iteration usage is retained separately for each role. -/
private def prepareRun (prepared : Generic.Prepared) (invocation : Invocation) :
    RunM (Generic.Prepared × Instance × List Instruction × List (Name × Nat)) := do
  let some body := invocation.definition.body | failAt invocation.location "refused" "external-protocol"
  let mut selections : List (Name × List (Name × Parameter)) := []
  let mut iterations : List (Name × Nat) := []
  -- Native entry construction runs each role's complete ingress in lexical order.
  for (role, store) in invocation.environments.mergeSort (fun a b => a.1 ≤ b.1) do
    for (name, value) in store do
      if value.public then
        validatePublic { invocation.location with scope :=
          { invocation.location.scope with role, site := name } } value
    modify fun state => { state with iterations := 0 }
    let mut parameters := []
    for (name, parameter) in invocation.binding.parameters.mergeSort (fun a b => a.1 ≤ b.1) do
      let count ← match parameter with
        | .constant n => pure n
        | .ingress bound selectors => do
            let selector ← checked invocation.location (lookup role (selectors.map fun s => (s.role, s)))
            let some function := prepared.typedFunctions.find? (·.name == selector.function)
              | failAt invocation.location "refused" "interactive-family-selector"
            let inputs ← checked invocation.location (selector.arguments.mapM fun n => lookup n store)
            let site := "ingress." ++ name
            let scope : Control.Scope := { invocation.location.scope with
              role := role, site := site, path := [.localCall site selector.function] }
            let location := { invocation.location with scope := scope }
            let result ← executeFunction location function inputs
            let [value] := result | failAt location "refused" "interactive-family-signature"
            let .index count ← checked location (value.toArithmetic .bls)
              | failAt location "refused" "interactive-family-signature"
            require location (count ≤ bound) "interactive-family-bound"
            pure count
      parameters := parameters ++ [(name, Parameter.constant count)]
    selections := selections ++ [(role, parameters)]
    iterations := iterations ++ [(role, (← get).iterations)]
  let (_, parameters) :: others := selections
    | failAt invocation.location "refused" "interactive-family-roles"
  require invocation.location (others.all (fun row => row.2 == parameters)) "interactive-family-disagreement"
  let binding := { invocation.binding with parameters }
  let instances := prepared.source.instances.map fun i => if i.name == binding.name then binding else i
  let source := { prepared.source with instances := instances }
  return ({ prepared with source := source }, binding, body, iterations)

def run (prepared : Generic.Prepared) (selected : Option Name) (invocation : Invocation) :
    Except Fault (List Value) × State := Id.run do
  let (preparation, state) := (prepareRun prepared invocation).run invocation.state
  match preparation with
  | .error fault => return (.error fault, closeRootFrame state (.error fault))
  | .ok (prepared, binding, body, iterations) =>
    let action : RunM (List Value) := do
      let underlying := services prepared invocation.location
      let values ← match selected with
        | some _ => do
            -- Close the selected root before fixture-completeness checks too.
            let execution := Control.executeBody underlying prepared.source selected
              limits.callDepth binding invocation.definition invocation.location.scope
              invocation.context invocation.environments body
            let (result, state) := execution.run (← get)
            set (closeRootFrame state result)
            match result with
            | .ok values => pure values
            | .error fault => throw fault
        | none => do
            let roles := (binding.roles.map Prod.snd).mergeSort (· ≤ ·)
            let participants := roles.map fun role =>
              let scope := { invocation.location.scope with role := role }
              let script := Control.executeBody (SourceControl.services invocation.location underlying)
                prepared.source (some role) limits.callDepth binding invocation.definition scope
                invocation.context (invocation.environments.filter (·.1 == role)) body
              ({ role, script, state := { iterations :=
                ((iterations.find? (·.1 == role)).map Prod.snd).getD 0 } } : SourceControl.Participant)
            let mut returned ← SourceControl.drive invocation.location prepared.source underlying 1000000
              [{ binding, scope := invocation.location.scope, body }] participants
            let mut values := []
            for (owner, _) in invocation.definition.results do
              let role ← checked invocation.location (binding.role owner)
              let value :: rest ← checked invocation.location (lookup role returned)
                | failAt invocation.location "refused" "reference-result-arity"
              values := values ++ [value]
              returned := returned.map fun (r, vs) => (r, if r == role then rest else vs)
            pure values
      require invocation.location (← get).replies.isEmpty "unused-replies"
      let state ← get
      require invocation.location (state.answers.size == state.usedAnswers.size) "unused-primitive-replies"
      return values
    -- The execution phase owns participant closure. Post-completion host fixture
    -- errors must not reopen or cancel already returned roots.
    return action.run state

def observe (selected : Option Name) (invocation : Invocation)
    (result : Except Fault (List Value) × State) : Json :=
  let outcome := match result.1 with
    | .ok values => .arr #[.str "returned", valuesJson values]
    | .error fault => .arr #[.str fault.reason, .str fault.detail, fault.location.json]
  .arr #[.str "zkc.reference-observation/1", .str invocation.location.entry,
    .str (selected.getD "joint"), outcome, .arr result.2.events,
    result.2.resourcesJson, .str (toString result.2.replies.length),
    .arr #[.str "scope", .str "source-control-and-typed-locals",
      .str (if selected.isNone then "tools-joint-schedule/1" else "open-role/1"),
      .str "external-group-contract", .str "logical-resources",
      .str "external-pcs-contract", .str "external-hash-contract",
      .str "no-physical-resource-correspondence", .str "no-elaboration-adequacy-proof"]]

def reference (source inputs : Json) (selected : Option Name) : Result Json := do
  let prepared ← Generic.prepareSource source
  let invocation ← invocation prepared selected inputs
  return observe selected invocation (run prepared selected invocation)

end Tools.Interactive.Reference
