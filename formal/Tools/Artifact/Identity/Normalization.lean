import Tools.Artifact.Identity.Resolution
import Tools.Artifact.Identity.Representation

/-! Bounded selected-protocol identity over the original generic carrier.
Formation is delegated to Generic.prepareSource by the public entry point.
This module resolves local binders, not types, and performs no specialization. -/

set_option autoImplicit false

namespace Tools.Artifact.Identity
open Lean (Json)
open Tools.Interactive

structure Scope where
  names : List (Name × Name) := []
  next : Nat := 0

def Scope.read (scope : Scope) (json : Json) : Result Json := do
  return .str (← lookup (← Decode.name json) scope.names)

def Scope.references (scope : Scope) (json : Json) : Result Json := do
  return array (← (← Decode.array json limits.ports).mapM scope.read)

def Scope.bind (scope : Scope) (json : Json) : Result (Json × Scope) := do
  let name ← Decode.name json
  ensure (!(scope.names.any fun p => p.1 == name)) "identity-ssa-rebinding"
  let fresh := s!"v{scope.next}"
  return (.str fresh, ⟨scope.names ++ [(name, fresh)], scope.next + 1⟩)

def Scope.binders (scope : Scope) (json : Json) : Result (Json × Scope) := do
  let mut scope := scope
  let mut names := []
  for name in ← Decode.array json limits.ports do
    let (name, next) ← scope.bind name
    names := names ++ [name]
    scope := next
  return (array names, scope)

/-- Binders are ordinal within a lexical scope. A loop starts a fresh scope;
its RHS references use the outer scope and its results extend that outer scope
only after the body. Capture pairs make the two scopes explicit in identity. -/
def normalizeBody (bindings : List OperationBinding) : Nat → Scope → Json → Result Json
  | 0, _, _ => .error "identity-body-depth"
  | depth + 1, initial, json => do
    let mut scope := initial
    let mut output := []
    for instruction in ← Decode.array json limits.instructions do
      let normalized ← match ← Decode.array instruction with
        | [.str "op", site, symbol, attributes, inputs, outputs] => do
            let binding ← lookup (← Decode.name symbol) (bindings.map fun b => (b.name, b))
            let inputs ← scope.references inputs
            let (outputs, next) ← scope.binders outputs
            scope := next
            let operation := (OperationContract.ofBinding binding).json
            pure (.arr #[.str "op", site, operation, attributes, inputs, outputs])
        | [.str "op", site, contract, arguments, attributes, inputs, outputs] => do
            let inputs ← scope.references inputs
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str "op", site, contract, arguments, attributes, inputs, outputs])
        | [.str "local", site, owner, callee, inputs, outputs] => do
            let inputs ← scope.references inputs
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str "local", site, owner, callee, inputs, outputs])
        | [.str "message", site, schema, sender, receiver, input, result] => do
            let input ← scope.read input
            let (result, next) ← scope.bind result
            scope := next
            pure (.arr #[.str "message", site, schema, sender, receiver, input, result])
        | [.str "apply", site, callee, arguments, inputs, outputs] => do
            let inputs ← scope.references inputs
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str "apply", site, callee, arguments, inputs, outputs])
        | [.str tag, site, callee, inputs, outputs] => do
            ensure (tag == "call") "identity-instruction"
            let inputs ← scope.references inputs
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str tag, site, callee, inputs, outputs])
        | [.str "if", site, condition, captures, yes, no, outputs] => do
            let condition ← scope.read condition
            let mut inner : Scope := {}
            let mut capturePairs := []
            for name in ← Decode.array captures limits.ports do
              let value ← scope.read name
              let (binder, next) ← inner.bind name
              inner := next
              capturePairs := capturePairs ++ [.arr #[binder, value]]
            let yes ← normalizeBody bindings depth inner yes
            let no ← normalizeBody bindings depth inner no
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str "if", site, condition, array capturePairs, yes, no, outputs])
        | [.str "for", site, induction, lower, upper, carried, captures, body, outputs] => do
            let lower ← scope.read lower
            let upper ← scope.read upper
            let (induction, inner) ← Scope.bind {} induction
            let mut inner := inner
            let mut pairs := []
            for pair in ← Decode.array carried limits.ports do
              let [binder, value] ← Decode.array pair | throw "identity-loop-pair"
              let value ← scope.read value
              let (binder, next) ← inner.bind binder
              inner := next
              pairs := pairs ++ [.arr #[binder, value]]
            let mut capturePairs := []
            for name in ← Decode.array captures limits.ports do
              let value ← scope.read name
              let (binder, next) ← inner.bind name
              inner := next
              capturePairs := capturePairs ++ [.arr #[binder, value]]
            let body ← normalizeBody bindings depth inner body
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str "for", site, induction, lower, upper, array pairs, array capturePairs, body, outputs])
        | [.str "loop", site, count, carried, captures, body, outputs] => do
            let mut inner : Scope := {}
            let mut pairs := []
            for pair in ← Decode.array carried limits.ports do
              let [binder, value] ← Decode.array pair | throw "identity-loop-pair"
              let value ← scope.read value
              let (binder, next) ← inner.bind binder
              inner := next
              pairs := pairs ++ [.arr #[binder, value]]
            let mut capturePairs := []
            for name in ← Decode.array captures limits.ports do
              let value ← scope.read name
              let (binder, next) ← inner.bind name
              inner := next
              capturePairs := capturePairs ++ [.arr #[binder, value]]
            let body ← normalizeBody bindings depth inner body
            let (outputs, next) ← scope.binders outputs
            scope := next
            pure (.arr #[.str "loop", site, count, array pairs, array capturePairs, body, outputs])
        | [.str "return", values] => pure (.arr #[.str "return", ← scope.references values])
        | [.str "yield", values] => pure (.arr #[.str "yield", ← scope.references values])
        | [.str "stop", _, _, _] => pure instruction
        | _ => throw "identity-instruction"
      output := output ++ [normalized]
    return array output

def normalizeDeclaration (bindings : List OperationBinding) (argumentIndex bodyIndex : Nat)
    (publicPorts : Bool) (record : Json) : Result Json := do
  let mut scope : Scope := {}
  let mut arguments := []
  for argument in ← Decode.array (← field record argumentIndex) limits.ports do
    let name ← field argument 0
    let (binder, next) ← scope.bind name
    scope := next
    let argument ← if publicPorts then pure argument else replace argument 0 binder
    arguments := arguments ++ [argument]
  let body ← normalizeBody bindings limits.depth scope (← field record bodyIndex)
  replace (← replace record argumentIndex (array arguments)) bodyIndex body

def recordsNamed (records : List Json) (names : List Name) : Result (List Json) := do
  let keyed ← records.mapM fun record => return (← recordName record, record)
  names.eraseDups.mapM fun name => lookup name keyed

/-- Admitted declaration names are ASCII source identifiers, whose String order
is also their UTF-8 byte order. Only the outer declaration groups are sorted. -/
def sorted (records : List Json) : Result Json := do
  let keyed ← records.mapM fun record => return (← recordName record, record)
  return array ((keyed.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd)

def protocolClosure (source : Source) (initial : List Name) : Result (List Name) := do
  let mut pending := initial.eraseDups
  let mut visited := []
  for _ in [:source.protocols.length + 1] do
    if pending.isEmpty then return visited
    let mut next := []
    for name in pending do
      let definition ← source.protocol name
      visited := name :: visited
      next := next ++ definition.dependencies.map Dependency.protocol
    pending := next.eraseDups.filter (fun name => !visited.contains name)
  throw "identity-protocol-closure-limit"

private def appliedNames : Nat → Json → Result (List Name)
  | 0, _ => .error "identity-body-depth"
  | depth + 1, body => do
      let names ← (← Decode.array body).mapM fun instruction => do
        match ← Decode.array instruction with
        | [.str "apply", _, .str callee, _, _, _] => return [callee]
        | [.str "if", _, _, _, yes, no, _] => return (← appliedNames depth yes) ++ (← appliedNames depth no)
        | [.str "for", _, _, _, _, _, _, nested, _] => appliedNames depth nested
        | _ => return []
      return names.flatten

def normalizedProtocol (original : Generic.Prepared) (resolved : Carrier) (entry : Name) : Result Json := do
  let source := original.source
  let root ← lookup entry source.entries
  let instances ← reachableFrom source root
  let initial ← instances.mapM fun name => return (← source.binding name).protocol
  let protocols ← protocolClosure source initial
  let calls ← protocols.mapM fun name => do
    Generic.localCalls limits.depth ((← source.protocol name).body.getD [])
  let calls := calls.flatten.eraseDups
  let ordinaryNames ← resolved.functions.mapM recordName
  let genericNames ← resolved.definitions.mapM recordName
  let mut functionsNeeded := []
  let mut definitionsNeeded := []
  let mut configurationsNeeded := []
  let mut visited := []
  let mut pending := calls
  for _ in [:resolved.functions.length + resolved.definitions.length + resolved.configurations.length + 1] do
    if pending.isEmpty then break
    let mut next := []
    for name in pending.eraseDups do
      if visited.contains name then continue
      visited := name :: visited
      if ordinaryNames.contains name || genericNames.contains name then
        let records := if ordinaryNames.contains name then resolved.functions else resolved.definitions
        let index := if ordinaryNames.contains name then 4 else 6
        if ordinaryNames.contains name then functionsNeeded := name :: functionsNeeded
        else definitionsNeeded := name :: definitionsNeeded
        let [record] ← recordsNamed records [name] | throw "identity-callee-reference"
        next := (← appliedNames limits.depth (← field record index)) ++ next
      else
        let configuration ← original.library.configuration name
        configurationsNeeded := name :: configurationsNeeded
        next := configuration.definition :: next
    pending := next.filter fun name => !visited.contains name
  ensure pending.isEmpty "identity-callee-closure-limit"
  let functions ← recordsNamed resolved.functions functionsNeeded
  let definitions ← recordsNamed resolved.definitions definitionsNeeded
  let configurations ← configurationsNeeded.mapM original.library.configuration
  let flattened ← configurations.mapM fun configuration => do
    let checked ← original.library.definition configuration.definition
    let arguments := checked.definition.parameters.filterMap fun (name, _) =>
      configuration.arguments.lookup name |>.map fun value => (name, value)
    return .arr #[.str "configure", .str configuration.name, .str configuration.definition,
      array (arguments.map fun (name, value) => strings [name, value]), .arr #[]]
  let .explicit bindings := source.environment
  let functions ← functions.mapM (normalizeDeclaration bindings 2 4 false)
  let definitions ← definitions.mapM (normalizeDeclaration [] 4 6 false)
  let protocols ← (← recordsNamed resolved.protocols protocols).mapM
    (normalizeDeclaration [] 4 7 true)
  let [entryRecord] ← recordsNamed resolved.entries [entry] | throw "identity-entry"
  return .arr #[.str "zkc.protocol-identity/1", entryRecord,
    ← sorted (← recordsNamed resolved.instances instances), ← sorted protocols,
    ← sorted functions, ← sorted definitions, ← sorted flattened]

end Tools.Artifact.Identity
