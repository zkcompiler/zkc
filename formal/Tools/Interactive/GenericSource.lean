import Tools.Interactive.GenericTypes
import Tools.Interactive.Admission

/-! Independent formation of original generic local declarations. Operations
retain source sites, static arguments and natural literals for later checking
against the actual candidate; no native symbol-generation algorithm is used. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic
open Lean (Json)
open Zkc.Source.Requirements

structure Operation where
  site : Name
  contract : String
  arguments : List Term
  attributes : List String
  inputs : List Name
  outputs : List Name
  application : Bool := false
  deriving Repr

structure Definition where
  name : Name
  parameters : Parameters
  requirements : List Predicate
  arguments : List (Name × ValueType)
  results : List ValueType
  operations : List Operation
  returns : List Name
  code : List Instruction := []
  deriving Repr

def Definition.instructions (definition : Definition) : List Instruction :=
  if definition.code.isEmpty then
    definition.operations.map (fun op => Instruction.op op.site op.site [] op.inputs op.outputs) ++ [.ret definition.returns]
  else definition.code

structure CheckedDefinition where
  definition : Definition
  obligations : List Predicate
  closure : Requirements.Closure definition.requirements

private def binder (json : Json) : Result Name := do
  let name ← Decode.name json
  ensure (!(name.contains '.')) "generic-binder"
  return name

private def decodeCode (parameters : Parameters) : Nat → Bool → Json → Result (List Operation × List Instruction)
  | 0, _, _ => .error "body-depth-limit"
  | depth + 1, region, json => do
      let terms := fun json => do
        (← Decode.array json limits.ports).mapM fun j => do parseTerm parameters (← Decode.string j)
      let mut operations := []
      let mut code := []
      for item in ← Decode.array json limits.instructions do
        match ← Decode.array item with
        | [.str "op", site, contract, args, attrs, inputs, outputs] =>
          let contract ← Decode.string contract
          let attrs ← (← Decode.array attrs).mapM Decode.string
          Bindings.attributes true contract attrs
          let op := Operation.mk (← Decode.name site) contract (← terms args) attrs
            (← Decode.names inputs) (← Decode.names outputs) false
          operations := operations ++ [op]
          code := code ++ [.op op.site op.site [] op.inputs op.outputs]
        | [.str "apply", site, callee, args, inputs, outputs] =>
          let op := Operation.mk (← Decode.name site) (← Decode.name callee) (← terms args) []
            (← Decode.names inputs) (← Decode.names outputs) true
          operations := operations ++ [op]
          code := code ++ [.op op.site op.site [] op.inputs op.outputs]
        | [.str "if", site, condition, captures, yes, no, outputs] =>
          let (yesOps, yes) ← decodeCode parameters depth true yes
          let (noOps, no) ← decodeCode parameters depth true no
          operations := operations ++ yesOps ++ noOps
          code := code ++ [.conditional (← Decode.name site) (← Decode.name condition) (← Decode.names captures)
            yes no (← Decode.names outputs)]
        | [.str "for", site, induction, lower, upper, carried, captures, body, outputs] =>
          let (ops, body) ← decodeCode parameters depth true body
          operations := operations ++ ops
          code := code ++ [.forLoop (← Decode.name site) (← Decode.name induction) (← Decode.name lower) (← Decode.name upper)
            (← Decode.pairs Decode.name Decode.name carried) (← Decode.names captures) body (← Decode.names outputs)]
        | [.str "yield", values] =>
          ensure region "local-terminal-context"
          code := code ++ [.yield (← Decode.names values)]
        | [.str "return", values] =>
          ensure (!region) "local-terminal-context"
          code := code ++ [.ret (← Decode.names values)]
        | _ => throw "generic-instruction"
      return (operations, code)

def decodeDefinition (json : Json) : Result Definition := do
  let [.str "generic_function", name, parameters, requirements, inputs, outputs, body] ← Decode.array json
    | throw "generic-definition"
  let parameters ← Decode.pairs binder (fun j => do Bindings.StaticSort.parse (← Decode.string j)) parameters
  ensure (parameters.length ≤ 128 && unique (parameters.map Prod.fst)) "generic-parameters"
  let terms := fun json => do
    (← Decode.array json limits.ports).mapM fun j => do parseTerm parameters (← Decode.string j)
  let requirements ← (← Decode.array requirements 4096).mapM fun item => do
    let [key, args] ← Decode.array item | throw "generic-predicate"
    predicate parameters (← Decode.string key) (← terms args)
  let arguments ← Decode.pairs (fun j => Decode.name j) (fun j => do valueType parameters (← Decode.string j)) inputs
  let results ← (← Decode.array outputs limits.ports).mapM fun j => do valueType parameters (← Decode.string j)
  let (operations, code) ← decodeCode parameters limits.depth false body
  let some (.ret returns) := code.getLast? | throw "generic-terminator"
  return ⟨← binder name, parameters, requirements, arguments, results, operations, returns, code⟩

private def bindValues (env : List (Name × ValueType)) (names : List Name)
    (types : List ValueType) : Result (List (Name × ValueType)) := do
  ensure (names.length == types.length) "generic-result-arity"
  ensure (unique names && names.all (fun n => !(env.any fun pair => pair.1 == n))) "generic-value-name"
  return env ++ names.zip types

private def consume (env : List (Name × ValueType)) (names used : List Name) : Result (List Name) := do
  let mut used := used
  for name in names do
    let ty ← lookup name env
    if ty.affine then
      ensure (!(used.contains name)) "generic-affine-reuse"
      used := name :: used
  return used

private def checkCode (definition : Definition) (application : Operation → Result Signature) :
    Nat → Bool → List (Name × ValueType) → Option (List ValueType) → List Instruction → Result (List ValueType × List Predicate)
  | 0, _, _, _, _ => .error "body-depth-limit"
  | depth + 1, region, initial, expected, code => do
      let mut env := initial
      let mut used := []
      let mut obligations := []
      let mut terminal := false
      let mut returned := []
      for instruction in code do
        ensure (!terminal) "instruction-after-terminal"
        match instruction with
        | .op site _ _ _ _ =>
          let op ← lookup site (definition.operations.map fun op => (op.site, op))
          let sig ← if op.application then application op else signature definition.parameters op.contract op.arguments
          ensure (op.inputs.length == sig.inputs.length) "generic-operand-arity"
          used ← consume env op.inputs used
          for (input, expected) in op.inputs.zip sig.inputs do
            obligations := obligations ++ (← typeEqualities (← lookup input env) expected)
          obligations := obligations ++ sig.needs
          env ← bindValues env op.outputs sig.outputs
        | .conditional _ condition captures yes no outputs =>
          obligations := obligations ++ (← typeEqualities (← lookup condition env) ⟨"bool", none⟩)
          used ← consume env captures used
          let captured ← captures.mapM fun name => do return (name, ← lookup name env)
          ensure (unique captures) "generic-value-name"
          let (types, needs) ← checkCode definition application depth true captured none yes
          let (_, otherNeeds) ← checkCode definition application depth true captured (some types) no
          obligations := obligations ++ needs ++ otherNeeds
          env ← bindValues env outputs types
        | .forLoop _ induction lower upper carried captures nested outputs =>
          for bound in [lower, upper] do
            obligations := obligations ++ (← typeEqualities (← lookup bound env) ⟨"index", none⟩)
          used ← consume env (carried.map Prod.snd) used
          let types ← (carried.map Prod.snd).mapM fun n => lookup n env
          let captured ← captures.mapM fun n => do return (n, ← lookup n env)
          ensure (captured.all fun p => !p.2.affine) "affine-capture"
          let inner ← bindValues [(induction, ⟨"index", none⟩)] (carried.map Prod.fst) types
          let inner ← bindValues inner captures (captured.map Prod.snd)
          let (_, needs) ← checkCode definition application depth true inner (some types) nested
          obligations := obligations ++ needs
          env ← bindValues env outputs types
        | .ret values | .yield values =>
          ensure (match instruction with | .yield _ => region | _ => !region) "local-terminal-context"
          let _ ← consume env values used
          returned ← values.mapM fun n => lookup n env
          if let some expected := expected then
            ensure (returned.length == expected.length) "generic-return-arity"
            for (actual, ty) in returned.zip expected do
              obligations := obligations ++ (← typeEqualities actual ty)
          terminal := true
        | _ => throw "generic-instruction"
      ensure terminal "generic-terminator"
      return (returned, obligations)

def checkDefinition (definition : Definition)
    (application : Operation → Result Signature := fun _ => .error "generic-callee") : Result CheckedDefinition := do
  ensure (unique (definition.operations.map Operation.site)) "generic-duplicate-site"
  bodyLimits definition.instructions
  ensure (definition.arguments.length ≤ limits.ports && unique (definition.arguments.map Prod.fst))
    "generic-arguments"
  let (_, obligations) ← checkCode definition application limits.depth false definition.arguments (some definition.results) definition.instructions
  let residual ← obligations.filterM fun p => return !(← groundRequirement p)
  let closure ← Requirements.check definition.requirements residual
  return ⟨definition, obligations, closure⟩

def formDefinition (json : Json) : Result CheckedDefinition := do
  checkDefinition (← decodeDefinition json)

end Tools.Interactive.Generic
