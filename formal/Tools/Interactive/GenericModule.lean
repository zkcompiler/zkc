import Tools.Interactive.Specialization
import Tools.Interactive.Algorithms
import Tools.Interactive.TypedLocal

/-! Source-owned nominal specialization for reference meaning and common
control checking. It keeps source configuration names, never native code hashes.
Every original declaration/configuration is formed; only demanded closed local
signatures enter the shared common protocol model. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic
open Lean (Json)

def localCalls : Nat → List Instruction → Result (List Name)
  | 0, _ => .error "body-depth-limit"
  | depth + 1, body => do
      let calls ← body.mapM fun instruction => do
        match instruction with
        | .localCall _ _ function _ _ => return [function]
        | .loop _ _ _ _ nested _ => localCalls depth nested
        | _ => return []
      return calls.flatten

structure Prepared where
  source : Source
  library : Library
  functions : List Explicit.Function
  typedFunctions : List TypedLocal.Function
  algorithmOrigins : List Algorithms.Origin

private structure Demand where
  bindings : List OperationBinding := []
  functions : List Explicit.Function := []
  reserved : List Name := []
  cache : List (String × Name) := []
  next : Nat := 0
  work : Nat := 0
  instructions : Nat := 0

private def instantiate (library : Library) : Nat → Configuration → StateT Demand Result Name
  | 0, _ => throw "algorithm-call-depth"
  | depth + 1, selected => do
      modify fun state => { state with work := state.work + 1 }
      ensure ((← get).work ≤ limits.instructions) "generic-specialization-limit"
      let checked ← library.definition selected.definition
      let args ← selected.closedArguments checked.definition
      let selected := { selected with
        arguments := args
        implementations := selected.implementations.mergeSort (fun a b => a.1 ≤ b.1) }
      let key := reprStr selected
      if let some name := (← get).cache.lookup key then return name
      modify fun state => { state with instructions := state.instructions + instructionCount limits.depth checked.definition.instructions }
      ensure ((← get).instructions ≤ limits.instructions) "generic-specialization-limit"
      ensure ((← get).functions.length < limits.definitions) "generic-specialization-limit"
      let mut name := selected.name
      if name.isEmpty then
        let state ← get
        let some fresh := (List.range (state.reserved.length + 1)).find? (fun i =>
          !(state.reserved.contains s!"reference_local_{state.next + i}"))
          | throw "generic-specialization-limit"
        name := s!"reference_local_{state.next + fresh}"
        modify fun state => { state with next := state.next + fresh + 1, reserved := name :: state.reserved }
      let mut callees := []
      for op in checked.definition.operations do
        if op.application then
          let (definition, target) ← applicationTarget
            (library.definitions.map CheckedDefinition.definition) library.configurations op.contract
          let substitution ← applicationArguments definition target.arguments checked.definition.parameters op.arguments
          let arguments ← substitution.mapM fun (parameter, term) => do
            let identity ← match constantIdentity term with
              | some identity => pure identity
              | none => termIdentity args term
            return (parameter, identity)
          let child ← instantiate library depth { target with name := "", arguments }
          callees := callees ++ [(op.site, child)]
      let (function, bindings) ← specialize { selected with name } checked (← get).reserved callees
      modify fun state => { state with
        functions := state.functions ++ [function]
        bindings := state.bindings ++ bindings
        cache := (key, name) :: state.cache
        reserved := state.reserved ++ bindings.map OperationBinding.name }
      ensure ((← get).bindings.length ≤ limits.definitions) "generic-specialization-limit"
      return name

private def prepareCode (library : Library) : Nat → Json → StateT Demand Result Json
  | 0, _ => throw "body-depth-limit"
  | depth + 1, body => do
    let body ← (← Decode.array body limits.instructions).mapM fun instruction => do
      match ← Decode.array instruction with
      | [.str "apply", site, callee, statics, inputs, outputs] =>
        let name ← Decode.name callee
        let actual ← (← Decode.array statics 128).mapM (fun j => do return ← Decode.string j)
        if library.configurations.any (fun c => c.name == name) ||
            library.definitions.any (fun d => d.definition.name == name) then
          let (definition, target) ← applicationTarget
            (library.definitions.map CheckedDefinition.definition) library.configurations name
          let remaining := definition.parameters.filter fun p => !(target.arguments.any fun q => q.1 == p.1)
          ensure (remaining.length == actual.length) "generic-static-arity"
          for ((_, sort), value) in remaining.zip actual do
            ensure (sort.accepts value) "generic-static-sort"
          let target := { target with
            name := if actual.isEmpty then name else ""
            arguments := target.arguments ++ (remaining.map Prod.fst).zip actual }
          let selected ← instantiate library 65 target
          return Json.arr #[.str "apply", site, .str selected, .arr #[], inputs, outputs]
        ensure actual.isEmpty "generic-static-arity"
        return instruction
      | [.str "match", site, input, captures, arms, outputs] =>
        let arms ← (← Decode.array arms 32).mapM fun arm => do
          let [label, payload, nested] ← Decode.array arm | throw "variant-arm"
          return Json.arr #[label, payload, ← prepareCode library depth nested]
        return Json.arr #[.str "match", site, input, captures, .arr arms.toArray, outputs]
      | [.str "if", site, condition, captures, yes, no, outputs] =>
        return Json.arr #[.str "if", site, condition, captures, ← prepareCode library depth yes,
          ← prepareCode library depth no, outputs]
      | [.str "for", site, induction, lower, upper, carried, captures, nested, outputs] =>
        return Json.arr #[.str "for", site, induction, lower, upper, carried, captures,
          ← prepareCode library depth nested, outputs]
      | _ => return instruction
    return Json.arr body.toArray

private def prepareCommon (library : Library) (json : Json) : StateT Demand Result Explicit.Module := do
  let [.str "zkc.protocol/1", bindings, functions, protocols, instances, entries] ← Decode.array json
    | throw "binding-common-source"
  let functions ← (← Decode.array functions limits.definitions).mapM fun function => do
    let [.str "function", name, args, results, body, origin] ← Decode.array function
      | throw "binding-function"
    let body ← prepareCode library limits.depth body
    return Json.arr #[.str "function", name, args, results, body, origin]
  Explicit.common (.arr #[.str "zkc.protocol/1", bindings, .arr functions.toArray, protocols, instances, entries])

/-- Prepare a library's common source. `executable` is what the caller is
asking about and is carried through to admission: a declaration is admitted
without an entry, an external body or an opaque port, and an executable
source is not. -/
def prepare (library : Library) (additionalCalls : List Name := [])
    (executable : Bool := true) : Result Prepared := do
  let [.str "zkc.protocol/1", bindings, functions, protocols, instances, entries] ← Decode.array library.common
    | throw "binding-common-source"
  let bindingNames ← (← Decode.array bindings).mapM fun j => do
    let name :: _ ← Decode.array j | throw "binding-declaration"
    Decode.name name
  let names ← ([functions, protocols, instances, entries].mapM fun j => do
    (← Decode.array j).mapM fun record => do
      let _ :: name :: _ ← Decode.array record | throw "generic-common-declaration"
      Decode.name name)
  let declared := bindingNames ++ names.flatten ++ library.configurations.map Configuration.name ++
    library.definitions.map (fun d => d.definition.name)
  ensure (unique declared) "generic-common-name-conflict"
  let action : StateT Demand Result Explicit.Module := do
    let common ← prepareCommon library library.common
    let calls ← common.source.protocols.mapM fun p => localCalls limits.depth (p.body.getD [])
    for callee in (calls.flatten ++ additionalCalls).eraseDups do
      if let some configuration := library.configurations.find? (fun c => c.name == callee) then
        let _ ← instantiate library 65 configuration
    return common
  let (common, demand) ← action.run { reserved := declared }
  let .explicit bindings := common.source.environment
  let bindings := bindings ++ demand.bindings
  let mut functions := common.functions ++ demand.functions
  let source := { common.source with environment := .explicit bindings, functions := functions.map Explicit.Function.code }
  let definitions := functions.map fun f => (f.code.name, (f.origin.map Explicit.Origin.definition).getD f.code.name)
  let (source, algorithmOrigins) ← Algorithms.expandWithOrigins source executable definitions
  functions ← functions.mapM fun f => do
    return { f with code := ← source.function f.code.name }
  let typed ← functions.mapM (TypedLocal.elaborate bindings)
  return ⟨source, library, functions, typed, algorithmOrigins⟩

def prepareSource (json : Json) (executable : Bool := true) : Result Prepared := do
  let library ← match ← Decode.array json with
    | .str "zkc.protocol/1" :: _ => pure (Library.mk [] [] json)
    | _ => library json
  prepare library [] executable

end Tools.Interactive.Generic
