import Tools.Interactive.Bindings
import Tools.Interactive.PhysicalFormation

/-! Full-type local syntax for explicit semantic/implementation bindings.
Control syntax is shared with the portable source language. -/

set_option autoImplicit false

namespace Tools.Interactive.Explicit
open Lean (Json)

structure Origin where
  definition : Name
  arguments : List (Name × String)
  deriving BEq, Repr

structure Function where
  code : Tools.Interactive.Function
  origin : Option Origin
  deriving BEq, Repr

def declaration (physical : Bool) (json : Json) : Result Bindings.Declaration := do
  let [name, contract, arguments, implementation] ← Decode.array json | throw "binding-declaration"
  let binding := OperationBinding.mk (← Decode.name name) (← Decode.string contract)
    (← (← Decode.array arguments 128).mapM Decode.string) (← Decode.string implementation)
  let _ ← Bindings.resolve physical binding
  return binding

def typeName (physical : Bool) (json : Json) : Result Ty := do
  let spelling ← Decode.string json
  let _ ← Bindings.valueType physical spelling
  return spelling

def decodeOrigin (json : Json) : Result (Option Origin) := do
  let items ← Decode.array json
  let [name, arguments] := items | throw "function-origin"
  let arguments ← Decode.pairs (fun j => Decode.name j) Decode.string arguments
  ensure (arguments.length ≤ 128 && unique (arguments.map Prod.fst) &&
    arguments.all (fun p => Bindings.staticIdentity p.2)) "function-origin"
  return some ⟨← Decode.name name, arguments⟩

def function (physical : Bool) (json : Json) (sourceLocal : Bool := false) : Result Function := do
  let [.str "function", name, arguments, results, body, origin] ← Decode.array json
    | throw "binding-function"
  let code := Tools.Interactive.Function.mk (← Decode.name name)
    (← Decode.pairs (fun j => Decode.name j) (typeName physical) arguments)
    (← (← Decode.array results limits.ports).mapM (typeName physical))
    (some (← Decode.body limits.depth .localFunction body (typeName physical) physical sourceLocal))
  return ⟨code, ← decodeOrigin origin⟩

structure Module where
  source : Source
  functions : List Function

def Module.names (module : Module) : List Name :=
  (match module.source.environment with
    | .explicit bindings => bindings.map OperationBinding.name) ++ module.source.functions.map Tools.Interactive.Function.name ++
    module.source.protocols.map Protocol.name ++ module.source.instances.map Instance.name ++
    module.source.entries.map Prod.fst

def common (json : Json) : Result Module := do
  let [.str "zkc.protocol/1", bindings, functions, protocols, instances, entries] ← Decode.array json
    | throw "binding-common-source"
  let bindings ← (← Decode.array bindings limits.definitions).mapM (declaration false)
  let functions ← (← Decode.array functions limits.definitions).mapM (fun j => function false j true)
  ensure (unique (bindings.map OperationBinding.name ++ functions.map (fun f => f.code.name))) "duplicate-symbol"
  let source : Source := ⟨.explicit bindings, functions.map Function.code,
    ← (← Decode.array protocols limits.definitions).mapM (fun j => Decode.protocol j (typeName false)),
    ← (← Decode.array instances limits.definitions).mapM Decode.binding,
    ← (← Decode.array entries limits.definitions).mapM Decode.entry⟩
  let result : Module := ⟨source, functions⟩
  ensure (unique result.names) "duplicate-symbol"
  return result

structure CandidateLocals where
  physical : Bool
  bindings : List Bindings.Declaration
  functions : List Function
  participants : Json
  entries : Json

/-- Local decoding alone does not admit participant control or source meaning. -/
def candidateLocals (json : Json) : Result CandidateLocals := do
  let [.str "zkc.participants/1", bindings, stage, functions, participants, entries] ← Decode.array json
    | throw "binding-candidate"
  let stage ← Decode.string stage
  ensure (stage == "logical" || stage == "physical") "unknown-stage"
  let physical := stage == "physical"
  let bindings ← (← Decode.array bindings limits.definitions).mapM (declaration physical)
  let functions ← (← Decode.array functions limits.definitions).mapM (function physical)
  if physical then
    for function in functions do PhysicalFormation.check bindings function.code
  ensure (unique (bindings.map OperationBinding.name ++ functions.map (fun f => f.code.name)))
    "duplicate-symbol"
  return ⟨physical, bindings, functions, participants, entries⟩

end Tools.Interactive.Explicit
