import Zkc.Source.FiniteControl
import Tools.Artifact.Runtime

/-! Direct original-source validator. No constructed program, projection,
generated origin manifest or prover store is an input to this interpreter. -/

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

abbrev Environment := List (Name × Value)

def values (environment : Environment) (names : List Name) : Result (List Value) :=
  names.mapM fun name => lookup name environment

def bind (environment : Environment) (names : List Name) (values : List Value) : Result Environment := do
  ensure (names.length == values.length && unique names &&
    names.all (fun name => !(environment.any fun p => p.1 == name))) "reference-binding"
  return names.zip values ++ environment

def ownedValues (owner : Name) (context : Context) (environment : Environment)
    (names : List Name) : Result (List Value) := do
  let ports ← context.read names
  values environment ((ports.filter fun p => p.owner == owner).map Port.name)

def bindOwned (owner : Name) (environment : Environment) (names : List Name)
    (ports : List (Name × Ty)) (results : List Value)  : Result Environment := do
  ensure (names.length == ports.length) "reference-result-ports"
  let retained := (names.zip ports).filter fun (_, role, _) => role == owner
  ensure (retained.map (fun (_, _, ty) => ty) == (← results.mapM (Value.typeFor))) "reference-result-types"
  bind environment (retained.map Prod.fst) results

private def localIndex (value : Value) : RunM Nat := do
  let .index n ← checked (value.toArithmetic .bls) | fail "refused" "local-bound-type"
  if n > limits.iterations then fail "exhausted" "local-bound-limit"
  return n

private def executeLocalBody (source : Source) (descriptor : Descriptor) : Nat → Location → Environment → List Instruction → RunM (List Value)
  | 0, _, _, _ => fail "exhausted" "local-stack-limit"
  | depth + 1, location, initial, instructions => do
      let mut environment := initial
      for instruction in instructions do
        match instruction with
        | .op site name attrs args results =>
            let location := { location with operation := site }
            let arguments ← checked (values environment args)
            let outputs ← evaluate source descriptor location name attrs arguments
            environment ← checked (bind environment results outputs)
        | .conditional site condition captures yes no outputs =>
            charge
            let .boolean selected ← checked (lookup condition environment) | fail "refused" "local-condition-type"
            let inputs ← checked (values environment captures)
            let location := { location with operation := site, path := location.path ++ [.localBranch site selected] }
            let results ← Zkc.Source.FiniteControl.branchM (fun _ => fail "refused" "local-control-stop") selected
              (fun _ => executeLocalBody source descriptor depth location (captures.zip inputs) yes)
              (fun _ => executeLocalBody source descriptor depth location (captures.zip inputs) no)
            environment ← checked (bind environment outputs results)
        | .forLoop site induction lower upper carried captures nested outputs =>
            charge
            let lower ← localIndex (← checked (lookup lower environment))
            let upper ← localIndex (← checked (lookup upper environment))
            let some bounds := Zkc.Source.FiniteControl.Bounds.admit lower upper limits.iterations
              | fail "exhausted" "local-bound-limit"
            let initial ← checked (values environment (carried.map Prod.snd))
            let captured ← checked (values environment captures)
            let (_, results) ← Zkc.Source.FiniteControl.iterateM (fun _ => fail "refused" "local-control-stop")
              bounds.count (bounds.lower, initial) fun (index, carriedValues) => do
                let location := { location with operation := site, path := location.path ++ [.localIteration site index] }
                if (← get).iterations ≥ 100000 then fail "exhausted" "local-iteration-limit"
                modify fun state => { state with iterations := state.iterations + 1 }
                let inputs := [(induction, Value.fromArithmetic .bls (.index index))] ++
                  (carried.map Prod.fst).zip carriedValues ++ captures.zip captured
                let results ← executeLocalBody source descriptor depth location inputs nested
                return (index + 1, results)
            environment ← checked (bind environment outputs results)
        | .ret results => return ← checked (values environment results)
        | .yield results =>
            charge
            return ← checked (values environment results)
        | _ => fail "refused" "invalid-local-body"
      fail "refused" "missing-local-return"

def executeLocal (source : Source) (descriptor : Descriptor) (location : Location)
    (function : Function) (arguments : List Value) : RunM (List Value) := do
  let some instructions := function.body | fail "refused" "external-function"
  let environment ← checked (bind [] (function.arguments.map Prod.fst) arguments)
  executeLocalBody source descriptor (limits.callDepth - location.path.length) location environment instructions

def readMessage (source : Source) (ty : Ty) (coordinate : ReceiveSite) : RunM Value := do
  let (length, cursor) ← checked ((← get).cursor.read 8)
  modify fun state => { state with cursor := cursor }
  let count := valueLE length
  require (count ≤ byteLimit) "proof-message-limit"
  let (bytes, cursor) ← checked ((← get).cursor.read count)
  modify fun state => { state with cursor := cursor }
  let value ← checked (decodeValue ty bytes)
  let selected ← if requiresSetup (← checked (value.typeFor)) then
      some <$> checked (selection coordinate (← get).setups.receives)
    else pure none
  validatePublic source value selected
  return value

def execute (source : Source) (descriptor : Descriptor) : Nat → Instance → Protocol →
    Location → Context → Environment → List Instruction → RunM (List Value)
  | 0, _, _, _, _, _, _ => fail "exhausted" "reference-stack-limit"
  | fuel + 1, binding, definition, location, initialContext, initialEnvironment, body => do
      let mut context := initialContext
      let mut environment := initialEnvironment
      for instruction in body do
        charge
        match instruction with
        | .localCall site owner name arguments results =>
            let sourceOwner := owner
            let owner ← checked (binding.role owner)
            let function ← checked (source.function name)
            let resultPorts := function.results.map fun ty => (owner, ty)
            if owner == descriptor.validator then
              let inputs ← checked (values environment arguments)
              let outputs ← executeLocal source descriptor
                { location with role := owner, sourceRole := sourceOwner, localSite := site, function := name }
                function inputs
              environment ← checked (bindOwned owner environment results resultPorts outputs)
            context ← checked (context.bind results resultPorts)
        | .message site schema sender receiver input output =>
            let logicalOrigin := location.message site schema sender receiver
            let sender ← checked (binding.role sender)
            let receiver ← checked (binding.role receiver)
            let port ← checked (context.get input)
            let value ← if receiver == descriptor.validator then
                readMessage source port.ty (binding.name, receiver, site)
              else if sender == descriptor.validator then
                checked (lookup input environment)
              else fail "refused" "construction-message-role"
            if receiver == descriptor.validator then
              environment ← checked (bind environment [output] [value])
            transcriptMessage logicalOrigin value
            context ← checked (context.bind [output] [(receiver, port.ty)])
        | .call site dependency arguments results =>
            let child ← checked (source.binding (← checked (lookup dependency binding.dependencies)))
            let childDefinition ← checked (source.protocol child.protocol)
            let (inputPorts, resultPorts) ← checked (callSignature source definition (some binding) dependency)
            if child.roles.any (fun p => p.2 == descriptor.validator) then
              let some childBody := childDefinition.body | fail "refused" "external-protocol"
              let inputs ← checked (ownedValues descriptor.validator context environment arguments)
              let childNames := childDefinition.arguments.map Port.name
              let childContext ← checked (Context.bind [] childNames inputPorts)
              let childEnvironment ← checked (bindOwned descriptor.validator [] childNames inputPorts inputs)
              let childLocation := { location with
                binding := child.name
                protocol := child.protocol
                path := location.path ++ [.call site child.name]
                localSite := ""
                function := ""
                operation := "" }
              let outputs ← execute source descriptor fuel child childDefinition childLocation
                childContext childEnvironment childBody
              environment ← checked (bindOwned descriptor.validator environment results resultPorts outputs)
            context ← checked (context.bind results resultPorts)
        | .loop site count carried captures nested results =>
            let count ← checked (binding.count count)
            let initial ← checked (context.read (carried.map Prod.snd))
            let ports := initial.map fun p => (p.owner, p.ty)
            let captured ← checked (context.read captures)
            let capturePorts := captured.map fun p => (p.owner, p.ty)
            let inner ← checked (Context.bind [] (carried.map Prod.fst) ports)
            let inner ← checked (inner.bind captures capturePorts)
            let captureValues ← checked (ownedValues descriptor.validator context environment captures)
            let mut carriedValues ← checked (ownedValues descriptor.validator context environment (carried.map Prod.snd))
            -- Range iteration is bounded by admission and the shared work budget;
            -- no entire unrolled source is constructed by this reference.
            for index in [:count] do
              if (← get).iterations ≥ 100000 then fail "exhausted" "local-iteration-limit"
              modify fun state => { state with iterations := state.iterations + 1 }
              charge
              let innerEnvironment ← checked (bindOwned descriptor.validator [] (carried.map Prod.fst) ports carriedValues)
              let innerEnvironment ← checked (bindOwned descriptor.validator innerEnvironment captures capturePorts captureValues)
              carriedValues ← execute source descriptor fuel binding definition
                { location with path := location.path ++ [.loop site index] }
                inner innerEnvironment nested
            environment ← checked (bindOwned descriptor.validator environment results ports carriedValues)
            context ← checked (context.bind results ports)
        | .ret names | .yield names =>
            return ← checked (ownedValues descriptor.validator context environment names)
        | .stop _ owner reason =>
            let owner ← checked (binding.role owner)
            if owner == descriptor.validator then fail reason "source-stop"
            else fail "incomplete" "foreign-stop-leaf"
        | _ => fail "refused" "invalid-common-body"
      fail "refused" "missing-common-return"

end Tools.Artifact
